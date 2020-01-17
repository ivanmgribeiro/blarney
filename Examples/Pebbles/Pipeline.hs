module Pipeline where 
-- 5-stage pipeline for 32-bit 3-operand register-based CPU.

import Blarney
import Blarney.BitScan
import Blarney.Stream

import CHERIBlarneyWrappers

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
    -- Source operand capabilities
  , opACap :: Bit 93
  , opBCap :: Bit 93
    -- Source register addresses
  , opAAddr :: RegId
  , opBAddr :: RegId
    -- Program counter interface
  , pc :: ReadWrite (Bit 32)
    -- TODO SCRs will go here (PCC, DDC, and the machine-mode CSRs)
    -- Write the instruction result
  , result :: WriteOnly (Bit 32)
  , resultCap :: WriteOnly (Bit 93)
    -- Indicate late result (i.e. computed in writeback rather than execute)
  , late :: WriteOnly (Bit 1)
    -- Keep track of whether we've encountered an exception
    -- TODO rename to trap in order to align with RVFI naming?
  , exc :: WriteOnly (Bit 1)
    -- special-cased SCRs
    -- TODO look into moving these into their own RAM (or adding to CSR RAM?)
  , pcc :: ReadWrite (Bit 93)
  , ddc :: ReadWrite (Bit 93)
  , mtcc :: ReadWrite (Bit 93)
  , mtdc :: ReadWrite (Bit 93)
  , mscratchc :: ReadWrite (Bit 93)
  , mepcc :: ReadWrite (Bit 93)
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
makeCPUPipeline :: Bool -> Config -> Stream (Bit 32) -> Module (RVFI_DII_Data)
makeCPUPipeline sim c dii_in = do
  -- Instruction memory
  let ext = if sim then ".hex" else ".mif"
  instrMem :: RAM InstrAddr Instr <- makeRAMInit ("prog" ++ ext)

  -- Two block RAMs allows two operands to be read,
  -- and one result to be written, on every cycle
  --regFileA :: RAM RegId (Bit 32) <- makeDualRAMForward 0
  --regFileB :: RAM RegId (Bit 32) <- makeDualRAMForward 0
  regFileA :: RAM RegId (Bit 93) <- makeDualRAMForward 0
  regFileB :: RAM RegId (Bit 93) <- makeDualRAMForward 0

  -- Instruction register
  instr :: Reg Instr <- makeReg dontCare

  -- Instruction operand registers
  regA :: Reg (Bit 93) <- makeReg dontCare
  regB :: Reg (Bit 93) <- makeReg dontCare

  -- Wire used to overidge the update to the PC,
  -- in case of a branch instruction
  pcNext :: Wire (Bit 32) <- makeWire dontCare

  -- Result of the execute stage
  resultWire :: Wire (Bit 93) <- makeWire dontCare
  postResultWire :: Wire (Bit 93) <- makeWire dontCare
  finalResultWire :: Wire (Bit 93) <- makeWire dontCare

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
  pc1 :: Reg (Bit 32) <- makeReg 0x80000000
  pc2 :: Reg (Bit 32) <- makeReg dontCare
  pc3 :: Reg (Bit 32) <- makeReg dontCare
  pc4 :: Reg (Bit 32) <- makeReg dontCare

  -- Capability program counters
  -- TODO optimise by removing unnecessary ones (if pcc permissions/offset/base etc don't
  -- change why store multiple?)
  -- TODO might need to add more PCCs
  pcc :: Reg (Bit 93) <- makeReg 0

  -- Capability SCRs
  --pcc :: Reg (Bit 93) <- makeReg almightyCap
  --ddc :: Reg (Bit 93) <- makeReg almightyCap
  --mtcc :: Reg (Bit 93) <- makeReg almightyCap
  pcc :: Reg (Bit 93) <- makeReg 0
  ddc :: Reg (Bit 93) <- makeReg 0
  mtcc :: Reg (Bit 93) <- makeReg 0
  mtdc :: Reg (Bit 93) <- makeReg 0
  mscratchc :: Reg (Bit 93) <- makeReg 0
  -- TODO make this start off with proper reset val
  mepcc :: Reg (Bit 93) <- makeReg 0


  -- TODO rename to trapWire to stay in line with RVFI naming?
  exc2_wire :: Wire (Bit 1) <- makeWire 0
  exc3_wire :: Wire (Bit 1) <- makeWire 0
  exc3_reg  :: Reg (Bit 1) <- makeReg 0
  exc4_wire :: Wire (Bit 1) <- makeWire 0
  exc4_reg  :: Reg (Bit 1) <- makeReg 0

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
  rvfi1 :: Reg (RVFI_Data) <- makeReg rvfi_base
  rvfi2 :: Reg (RVFI_Data) <- makeReg rvfi_base
  rvfi3 :: Reg (RVFI_Data) <- makeReg rvfi_base
  rvfi4 :: Reg (RVFI_Data) <- makeReg rvfi_base

  regCounter :: Reg (Bit 5) <- makeReg 0
  started :: Reg (Bit 1) <- makeReg 0

  always do
    -- startup sequence
    -- TODO clean this up by using go's properly
    -- (see https://github.com/mn416/blarney/pull/23)
    when (started.val.inv) do
      store regFileA (regCounter.val) if regCounter.val .==. 0
                                      then nullCap
                                      else almightyCap
      store regFileB (regCounter.val) if regCounter.val .==. 0
                                      then nullCap
                                      else almightyCap
      regCounter <== regCounter.val + 1
      --display "initialising register " (regCounter.val)

    when (regCounter.val .==. 31) do
      started <== 1
      pcc <== almightyCap
      ddc <== almightyCap
      mepcc <== lower ((almightyCap.setAddr) (0x00000000))
      mtcc <== almightyCap
      mtdc <== nullCap
      mscratchc <== nullCap
      --display "finished starting up"

    when (started.val) do
      --display "clocking core"


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

      -- select correct PC to fetch
      let pcFetch = pcNext.active ?  (pcNext.val,
                                     (stallWire.val .|. dii_in.canPeek.inv) ? (pc1.val,
                                                                               pc1.val + 4))
      --display "pcfetch: " pcFetch
      --display "pc1: " (pc1.val)
      --display "pc2: " (pc2.val)
      --display "exc4 " (exc4_wire.val)
      --display "pcNext.active " (pcNext.active)
      --display "pcNext.val " (pcNext.val)
      pc1 <== pcFetch

      -- TODO perform pcc checks here and propagate exception

      -- Index the instruction memory
      let instrAddr = lower (range @31 @2 pcFetch)
      load instrMem instrAddr

      -- trigger stage 1 when instruction fetch has returned
      let go1 :: Bit 1 = dii_in.canPeek


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
        (rvfi_base) {
            rvfi_insn = instrData,
            rvfi_rs1_addr = (srcA c (instrData)),
            rvfi_rs2_addr = (srcB c (instrData)),
            rvfi_pc_rdata = pc1.val,
            rvfi_pc_wdata = pc1.val + 4
        }
      else
        rvfi_base

      --display "rvfi1: " (rvfi1.val)
      --display "\n"


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
              opA       = getAddr a
            , opB       = getAddr b
            , opACap    = a
            , opBCap    = b
            , opAAddr   = (c.srcA) (instr2.val)
            , opBAddr   = (c.srcB) (instr2.val)
            , pc        = ReadWrite (pc2.val) (error "Can't write PC in pre-execute")
            , result    = error "Can't write result in pre-execute"
            , resultCap = error "Can't write resultCap in pre-execute"
            , late      = WriteOnly (lateWire <==)
            , exc       = WriteOnly (exc2_wire <==)
            -- TODO what happens if i set the pcc to something that is unrepresentable
            , pcc       = ReadWrite (lower (setAddr (pcc.val) (pc2.val))) (error "cant write pcc")
            , ddc       = ReadWrite (ddc.val) (error "cant write ddc")
            , mtcc      = ReadWrite (mtcc.val) (mtcc <==)
            , mtdc      = ReadWrite (mtdc.val) (mtdc <==)
            , mscratchc = ReadWrite (mscratchc.val) (mscratchc <==)
            , mepcc     = ReadWrite (mepcc.val) (mepcc <==)
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

      --display "rvfi2: " (rvfi2.val)
      --display "\n"

      -- Stage 3: Execute
      -- ================

      -- State for execute stage
      let state = State {
              opA    = getAddr (regA.val)
            , opB    = getAddr (regB.val)
            , opACap = regA.val
            , opBCap = regB.val
            , opAAddr   = (c.srcA) (instr3.val)
            , opBAddr   = (c.srcB) (instr3.val)
            , pc     = ReadWrite (pc3.val) (\x -> when (exc4_wire.val.inv) do pcNext <== x)
            , result = WriteOnly $ \x ->
                         when (dst c (instr3.val) .!=. 0) do
                           resultWire <== nullWithAddr x
                           display "################ writing 0x" x
                           display "in stage 3"
            , resultCap = WriteOnly $ \x ->
                            when (dst c (instr3.val) .!=. 0) do
                              resultWire <== x
                              display "writing in stage 3"
            , late   = error "Cant write late signal in execute"
            , exc    = WriteOnly (exc3_wire <==)
            , pcc       = ReadWrite (lower (setAddr (pcc.val) (pc3.val))) (pcc <==)
            , ddc       = ReadWrite (ddc.val) (ddc <==)
            , mtcc      = ReadWrite (mtcc.val) (mtcc <==)
            , mtdc      = ReadWrite (mtdc.val) (mtdc <==)
            , mscratchc = ReadWrite (mscratchc.val) (mscratchc <==)
            , mepcc     = ReadWrite (mepcc.val) (mepcc <==)
            }

      -- Execute rules
      when (go3.val .&. exc4_wire.val.inv) do
        matchDefault (instr3.val) (execRules c state) (exc3_wire <== 1)
        --match (instr3.val) (execRules c state)
        go4 <== go3.val .&. (exc3_wire.val.inv .|. exc3_reg.val.inv) .&. (exc4_wire.val.inv)
        -- set RVFI mem info here or in the instruction definitions?

      instr4 <== instr3.val

      -- set RVFI register values
      rvfi3 <== (rvfi2.val) {
          rvfi_rs1_data = getAddr (regA.val),
          rvfi_rs2_data = getAddr (regB.val),
          rvfi_pc_wdata = if (pcNext.active) then pcNext.val else rvfi2.val.rvfi_pc_wdata
      }

      exc4_reg <== (exc3_wire.val) .|. (exc3_reg.val)
      pc4 <== pc3.val

      --display "overwrite pc_wdata? ans: " (pcNext.active)
      --display "rvfi3: " (rvfi3.val)
      --display "\n"


      -- Stage 4: Writeback
      -- ==================

      -- State for post-execute stage
      let state = State {
              opA    = getAddr (regA.val.old)
            , opB    = getAddr (regB.val.old)
            , opACap = regA.val.old
            , opBCap = regB.val.old
            , opAAddr   = (c.srcA) (instr4.val)
            , opBAddr   = (c.srcB) (instr4.val)
            --, pc     = ReadWrite (error "cant read pc in post-execute") (pcNext <==)
            , pc     = ReadWrite (pc4.val) (pcNext <==)
            , resultCap = WriteOnly $ \x ->
                            when (dst c (instr4.val) .!=. 0) do
                              postResultWire <== x
                              display "writing in stage 4"
            , result = WriteOnly $ \x ->
                         when (dst c (instr4.val) .!=. 0) do
                           postResultWire <== nullWithAddr x
                           display "################ writing 0x" x
                           display "in stage 4"
            , late   = error "Can't write late signal in post-execute"
            , exc    = WriteOnly (exc4_wire <==)
            , pcc       = ReadWrite (lower (setAddr (pcc.val) (pc4.val))) (pcc <==)
            , ddc       = ReadWrite (ddc.val) (error "cant write ddc")
            , mtcc      = ReadWrite (mtcc.val) (mtcc <==)
            , mtdc      = ReadWrite (mtdc.val) (mtdc <==)
            , mscratchc = ReadWrite (mscratchc.val) (mscratchc <==)
            , mepcc     = ReadWrite (mepcc.val) (mepcc <==)
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
      when ((finalResultWire.active) .&. exc4_wire.val.inv .&. (delay 0 (exc4_wire.val.inv))) do
        store regFileA rd (finalResultWire.val)
        store regFileB rd (finalResultWire.val)
        display "wrote 0x" (finalResultWire.val) " to x" rd

      -- set RVFI register write value
      let rvfifinal = (rvfi3.val) { rvfi_valid = go4.val .|. exc4_wire.val .|. exc4_reg.val
                                  , rvfi_rd_wdata = (getAddr rvfiRes)
                                  , rvfi_trap = (exc4_wire.val .|. exc4_reg.val)
                                  , rvfi_pc_wdata = if (exc4_wire.val) then
                                                      pcNext.val
                                                    else
                                                      rvfi3.val.rvfi_pc_wdata
                                  }

      rvfi4 <== rvfifinal

      display "\n"
      display "instructions in pipeline: "
      display "stage 1: " (instrData)
      display "stage 2: " (instr2.val)
      display "stage 3: " (instr3.val)
      display "stage 4: " (instr4.val)
      display "\n"


      --display "overwrite pc_wdata? ans: " (exc4_wire.val)
      display "rvfi4: " (rvfifinal)
      --display "\n"

  return RVFI_DII_Data { rvfi_data = rvfi4.val
                       , flush = exc3_wire.val .|. exc3_reg.val .|. pcNext.active
                       , flush4 = exc4_wire.val
                       , go4 = go4.val
                       }
