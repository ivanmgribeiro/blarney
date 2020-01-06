module Pipeline where 
-- 5-stage pipeline for 32-bit 3-operand register-based CPU.

import Blarney
import Blarney.BitScan
import Blarney.Stream

import RVFI_DII

-- Instructions
type Instr = Bit 32

-- Register identifiers
type RegId = Bit 5

-- Instruction memory size
type InstrAddr = Bit 14

-- Pipeline configuration
data Config =
  Config {
    -- Get source register A
    srcA :: Instr -> RegId
    -- Get source register B
  , srcB :: Instr -> RegId
    -- Get destination register
  , dst :: Instr -> RegId
    -- Dispatch rules for pre-execute stage
  , preExecRules :: State -> [Instr -> Action (Bit 1)]
    -- Dispatch rules for execute stage
  , execRules :: State -> [Instr -> Action (Bit 1)]
    -- Dispatch rules for post-execute stage
  , postExecRules :: State -> [Instr -> Action (Bit 1)]
  }

-- Pipeline state, visisble to the ISA
data State =
  State {
    -- Source operands
    opA :: Bit 32
  , opB :: Bit 32
    -- Program counter interface
  , pc :: ReadWrite (Bit 32)
    -- Write the instruction result
  , result :: WriteOnly (Bit 32)
    -- Indicate late result (i.e. computed in writeback rather than execute)
  , late :: WriteOnly (Bit 1)
    -- Keep track of whether we've encountered an exception
    -- TODO rename to trap in order to align with RVFI naming?
  , exc :: WriteOnly (Bit 1)
  }

rvfi_base :: RVFI_Data = RVFI_Data {
    rvfi_valid      = 0,
    rvfi_pc_rdata   = 0,
    rvfi_pc_wdata   = 0,
    rvfi_insn       = 0,
    rvfi_rs1_data   = 0,
    rvfi_rs2_data   = 0,
    rvfi_rd_wdata   = 0,
    rvfi_mem_addr   = 0,
    rvfi_mem_rdata  = 0,
    rvfi_mem_wdata  = 0,
    rvfi_mem_rmask  = 0,
    rvfi_mem_wmask  = 0,
    rvfi_rs1_addr   = 0,
    rvfi_rs2_addr   = 0,
    rvfi_rd_addr    = 0,
    rvfi_trap       = 0
}

-- Pipeline
-- makeCPUPipeline :: Bool -> Config -> Module ()
makeCPUPipeline :: Bool -> Config -> Stream (Bit 32) -> Module (RVFI_DII_Data)
makeCPUPipeline sim c dii_in = do
  -- Instruction memory
  let ext = if sim then ".hex" else ".mif"
  instrMem :: RAM InstrAddr Instr <- makeRAMInit ("prog" ++ ext)

  -- Two block RAMs allows two operands to be read,
  -- and one result to be written, on every cycle
  regFileA :: RAM RegId (Bit 32) <- makeDualRAMForward 0
  regFileB :: RAM RegId (Bit 32) <- makeDualRAMForward 0

  -- Instruction register
  instr :: Reg Instr <- makeReg dontCare

  -- Instruction operand registers
  regA :: Reg (Bit 32) <- makeReg dontCare
  regB :: Reg (Bit 32) <- makeReg dontCare

  -- Wire used to overidge the update to the PC,
  -- in case of a branch instruction
  pcNext :: Wire (Bit 32) <- makeWire dontCare

  -- Result of the execute stage
  resultWire :: Wire (Bit 32) <- makeWire dontCare
  postResultWire :: Wire (Bit 32) <- makeWire dontCare
  finalResultWire :: Wire (Bit 32) <- makeWire dontCare

  -- Pipeline stall
  -- signals that the result from the instruction in stage 3 will only be available
  -- in stage 4
  lateWire :: Wire (Bit 1) <- makeWire 0
  -- signals that stages 1 & 2 should wait for the result to the instruction currently in
  -- stage 3 to come back since the instruction in stage 2 needs it
  stallWire :: Wire (Bit 1) <- makeWire 0

  -- Cycle counter
  count :: Reg (Bit 32) <- makeReg 0
  always (count <== count.val + 1)

  -- Program counters for each pipeline stage
  --pc1 :: Reg (Bit 32) <- makeReg 0xfffffffc
  --pc1 :: Reg (Bit 32) <- makeReg 0x7ffffffc
  pc1 :: Reg (Bit 32) <- makeReg 0x80000000
  pc2 :: Reg (Bit 32) <- makeReg dontCare
  pc3 :: Reg (Bit 32) <- makeReg dontCare

  -- TODO rename to trapWire to stay in line with RVFI naming?
  exc2_wire :: Wire (Bit 1) <- makeWire 0
  exc3_wire :: Wire (Bit 1) <- makeWire 0
  exc3_reg  :: Reg (Bit 1) <- makeDReg 0
  exc4_wire :: Wire (Bit 1) <- makeWire 0
  exc4_reg  :: Reg (Bit 1) <- makeDReg 0

  -- Instruction registers for pipeline stages 2 and 3 and 4
  instr2 :: Reg Instr <- makeReg 0
  instr3 :: Reg Instr <- makeReg 0
  instr4 :: Reg Instr <- makeReg 0

  -- Triggers for pipeline stages 2 and 3
  go2 :: Reg (Bit 1) <- makeDReg 0
  go3 :: Reg (Bit 1) <- makeDReg 0
  go4 :: Reg (Bit 1) <- makeDReg 0

  -- TODO changed, rename this later
  retval :: Wire (Bit 1) <- makeWire 0

  -- TODO check this stuff
  -- RVFI registers
  rvfi0 :: Reg (RVFI_Data) <- makeDReg rvfi_base
  rvfi1 :: Reg (RVFI_Data) <- makeDReg rvfi_base
  rvfi2 :: Reg (RVFI_Data) <- makeDReg rvfi_base
  rvfi3 :: Reg (RVFI_Data) <- makeDReg rvfi_base
  rvfi4 :: Reg (RVFI_Data) <- makeDReg rvfi_base

  always do
    -- Stage 0: Instruction Fetch
    -- ==========================

    -- get instruction data
    let instrData = dii_in.peek

    -- consume only when ready to receive an instruction
    when ((dii_in.canPeek)
          .&. (stallWire.val.inv)
          .&. (exc3_wire.val.inv)
          .&. (exc3_wire.val.inv)
          .&. (pcNext.active.inv)) do
              dii_in.consume
    -- when ((dii_in.canPeek) .&. (stallWire.val.inv) .&. (exc3_wire.val.inv) .&. (exc3_wire.val.inv) .&. (pcNext.active.inv)) do display "consumed instruction: 0x" (instrData)


    -- select correct PC to fetch
    let pcFetch = pcNext.active ?  (pcNext.val,
                                   (stallWire.val .|. dii_in.canPeek.inv) ? (pc1.val,
                                                                             pc1.val + 4))
    pc1 <== pcFetch

    -- Index the instruction memory
    let instrAddr = lower (slice @31 @2 pcFetch)
    load instrMem instrAddr

    -- Always trigger stage 1, except on first cycle
    --let go1 :: Bit 1 = reg 0 1

    -- trigger stage 1 when instruction fetch has returned
    let go1 :: Bit 1 = dii_in.canPeek


    -- set RVFI values for this stage
    rvfi0 <== rvfi_base {
        rvfi_pc_rdata = pcFetch,
        rvfi_pc_wdata = pcFetch + 4
    }


    -- Stage 1: Operand Fetch
    -- ======================

    -- Trigger stage 2, except on pipeline flush or stall
    -- TODO do i need to include exception wires here?
    let go2_cond = pcNext.active.inv .&. stallWire.val.inv
    when go1 do
      go2 <== go2_cond

    -- Fetch operands
    load regFileA (srcA c (instrData))
    load regFileB (srcB c (instrData))

    -- Latch instruction and PC for next stage
    instr2 <== instrData
    pc2 <== pc1.val

    -- set RVFI register addresses
    rvfi1 <== if go2_cond then
      (rvfi0.val) {
          rvfi_insn = instrData,
          rvfi_rs1_addr = (srcA c (instrData)),
          rvfi_rs2_addr = (srcB c (instrData))
      }
    else
      rvfi0.val


    -- Stage 2: Latch Operands
    -- =======================
  
    -- Register forwarding logic
    -- forward from stage 3
    let forward rS other =
         (resultWire.active .&. (dst c (instr3.val) .==. instr2.val.rS)) ?
         (resultWire.val, other)

    -- forward from stage 4
    let forward' rS other =
         (finalResultWire.active .&.
           (dst c (instr4.val) .==. instr2.val.rS)) ?
             (finalResultWire.val, other)

    -- Register forwarding
    let a = forward (c.srcA) (forward' (c.srcA) (regFileA.out))
    let b = forward (c.srcB) (forward' (c.srcB) (regFileB.out))

    -- Latch operands
    regA <== a
    regB <== b

    -- State for pre-execute stage
    let state = State {
            opA    = a
          , opB    = b
          , pc     = ReadWrite (pc2.val) (error "Can't write PC in pre-execute")
          , result = error "Can't write result in pre-execute"
          , late   = WriteOnly (lateWire <==)
          , exc    = WriteOnly (exc2_wire <==)
          }

    -- Pre-execute rules
    -- TODO: potential performance improvement: can check for illegal instructions here.
    --       currently only checked in stage 3 for simplicity of exception implementation
    when (go2.val) do
      match (instr2.val) (preExecRules c state)

    -- Pipeline stall
    -- stall stages 1 & 2 while waiting for the result to come back
    when (lateWire.val) do
      when ((srcA c (instrData) .==. dst c (instr2.val)) .|.
            (srcB c (instrData) .==. dst c (instr2.val))) do
                stallWire <== true

    -- Latch instruction and PC for next stage
    instr3 <== instr2.val
    pc3 <== pc2.val

    -- Trigger stage 3, except on pipeline flush
    let go3_cond = pcNext.active.inv
    when (go3_cond) do
      go3 <== go2.val

    -- Pass on RVFI register
    rvfi2 <== if go3_cond then rvfi1.val else rvfi2.val

    -- TODO this might need to be stalled as well
    exc3_reg <== exc2_wire.val

    -- Stage 3: Execute
    -- ================

    -- State for execute stage
    let state = State {
            opA    = regA.val
          , opB    = regB.val
          , pc     = ReadWrite (pc3.val) (\x -> when (exc4_wire.val.inv) do pcNext <== x)
          , result = WriteOnly $ \x ->
                       when (dst c (instr3.val) .!=. 0) do
                         resultWire <== x
          , late   = error "Cant write late signal in execute"
          , exc    = WriteOnly (exc3_wire <==)
          }

    -- Execute rules
    when (go3.val) do
      matchDefault (instr3.val) (execRules c state) (exc3_wire <== 1)
      --match (instr3.val) (execRules c state)
      go4 <== go3.val .&. (exc3_wire.val.inv .|. exc3_reg.val.inv) .&. (exc4_wire.val.inv)
      -- set RVFI mem info here or in the instruction definitions?

    instr4 <== instr3.val

    -- set RVFI register values
    rvfi3 <== (rvfi2.val) {
        rvfi_rs1_data = regA.val,
        rvfi_rs2_data = regB.val,
        rvfi_pc_wdata = if (pcNext.active) then pcNext.val else rvfi2.val.rvfi_pc_wdata
    }

    display "executing 0x" (instr3.val)
    --when (exc3_wire.val .|. exc3_reg.val) do
    --    display "@@@@@@@@@ exception at stage 3 on instruction 0x" (instr3.val)

    --when (exc3_wire.val .|. exc3_reg.val .|. pcNext.active) do
    --    display "[][][][][][][][][][][][][] FLUSHING PIPELINE" (instr3.val)

    exc4_reg <== (exc3_wire.val) .|. (exc3_reg.val)

    -- Stage 4: Writeback
    -- ==================

    -- State for post-execute stage
    let state = State {
            opA    = regA.val.old
          , opB    = regB.val.old
          --, pc     = error "Can't access PC in post-execute"
          -- TODO what happens if there's an exception in stage 4 and a jump in stage 3?
          , pc     = ReadWrite (error "cant read pc in post-execute") (pcNext <==)
          , result = WriteOnly $ \x ->
                       when (dst c (instr4.val) .!=. 0) do
                         postResultWire <== x
          , late   = error "Can't write late signal in post-execute"
          , exc    = WriteOnly (exc4_wire <==)
          }

    -- Post-execute rules
    when (go4.val) do
      match (instr4.val) (postExecRules c state)

    -- Determine final result destination
    let rd = dst c (instr4.val)

    let rvfiRes = if postResultWire.active
                    then postResultWire.val
                  else if postResultWire.active.inv .&. delay 0 (resultWire.active)
                    then resultWire.val.old
                  else
                    0

    when (postResultWire.active) do
      finalResultWire <== postResultWire.val
    when (postResultWire.active.inv .&. delay 0 (resultWire.active)) do
      finalResultWire <== resultWire.val.old


    -- Writeback
    when ((finalResultWire.active) .&. (exc4_wire.val.inv) .&. (exc4_reg.val.inv)) do
      store regFileA rd (finalResultWire.val)
      store regFileB rd (finalResultWire.val)

    -- set RVFI register write value
    let rvfifinal = (rvfi3.val) { rvfi_valid = go4.val .|. exc4_wire.val .|. exc4_reg.val
                                , rvfi_rd_wdata = (rvfiRes)
                                , rvfi_trap = (exc4_wire.val .|. exc4_reg.val)
                                , rvfi_pc_wdata = if (exc4_wire.val) then
                                                    pcNext.val
                                                  else
                                                    rvfi3.val.rvfi_pc_wdata
                                }

    rvfi4 <== rvfifinal

    --when (exc4_wire.val .|. exc4_reg.val) do
    --    display "@@@@@@@@@ exception in stage 4 on instruction 0x" (instr4.val)


    --display $ rvfi4.val
    --display "\n\n"

    ----when (exc3_wire.val .==. 1) do
    --display "pipeline state when instruction 0x" (instr3.val) " is fed in"
    --display (instrData) ", go1: " (go1)
    --display (instr2.val) ", go2: " (go2.val)
    --display (instr3.val) ", go3: " (go3.val)
    --display (instr4.val) ", go4: " (go4.val)
    --display "\n\n"



  return RVFI_DII_Data { rvfi_data = rvfi4.val
                       , flush = exc3_wire.val .|. exc3_reg.val .|. pcNext.active
                       , flush4 = exc4_wire.val
                       , go4 = go4.val
                       }
