module Pipeline where

-- 5-stage pipeline for 32-bit 3-operand register-based CPU.

import Blarney
import Blarney.RAM
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
  }

rvfi_base :: RVFI_DII_Data = RVFI_DII_Data {
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

  -- deal with DDII
  -- TODO rewrite this?
  -- let instrData = instrMem.out

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
  lateWire :: Wire (Bit 1) <- makeWire 0
  stallWire :: Wire (Bit 1) <- makeWire 0

  -- Cycle counter
  count :: Reg (Bit 32) <- makeReg 0
  always (count <== count.val + 1)

  -- Program counters for each pipeline stage
  --pc1 :: Reg (Bit 32) <- makeReg 0xfffffffc
  pc1 :: Reg (Bit 32) <- makeReg 0x7ffffffc
  pc2 :: Reg (Bit 32) <- makeReg dontCare
  pc3 :: Reg (Bit 32) <- makeReg dontCare

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
  rvfi1 :: Reg (RVFI_DII_Data) <- makeDReg rvfi_base
  rvfi2 :: Reg (RVFI_DII_Data) <- makeDReg rvfi_base
  rvfi3 :: Reg (RVFI_DII_Data) <- makeDReg rvfi_base
  rvfi4 :: Reg (RVFI_DII_Data) <- makeDReg rvfi_base
  rvfifinal :: Reg (RVFI_DII_Data) <- makeDReg rvfi_base

  always do
    -- Stage 0: Instruction Fetch
    -- ==========================

    -- PC to fetch
    let instrData = dii_in.peek

    when ((dii_in.canPeek) .&. (stallWire.val.inv)) do dii_in.consume
    when ((dii_in.canPeek) .&. (stallWire.val.inv)) do display "consumed instruction: 0x" (instrData)
    when ((dii_in.canPeek) .&. (stallWire.val.inv)) do display "state: " (dii_in.canPeek) " " (stallWire.val.inv)


    let pcFetch = pcNext.active ?
                    (pcNext.val, (stallWire.val .|. dii_in.canPeek.inv) ? (pc1.val, pc1.val + 4))
    pc1 <== pcFetch

    -- Index the instruction memory
    let instrAddr = lower (range @31 @2 pcFetch)
    load instrMem instrAddr

    -- Always trigger stage 1, except on first cycle
    --let go1 :: Bit 1 = reg 0 1
    let go1 :: Bit 1 = dii_in.canPeek


    -- TODO set RVFI PC RData (and instruction?)
    rvfi1 <== rvfi_base {
        rvfi_pc_rdata = pcFetch,
        rvfi_pc_wdata = pcFetch + 4,
        rvfi_insn = instrData
    }


    -- Stage 1: Operand Fetch
    -- ======================

    -- Trigger stage 2, except on pipeline flush or stall
    when go1 do
      when (pcNext.active.inv .&. stallWire.val.inv) do
        go2 <== 1

    -- Fetch operands
    load regFileA (srcA c (instrData))
    load regFileB (srcB c (instrData))

    -- Latch instruction and PC for next stage
    instr2 <== instrData
    pc2 <== pc1.val

    -- TODO set RVFI register addresses
    rvfi2 <== (rvfi1.val) {
        rvfi_rs1_addr = (srcA c (instrData)),
        rvfi_rs2_addr = (srcB c (instrData))
    }

    -- Stage 2: Latch Operands
    -- =======================
  
    -- Register forwarding logic
    let forward rS other =
         (resultWire.active .&. (dst c (instr3.val) .==. instr2.val.rS)) ?
         (resultWire.val, other)

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
          }

    -- Pre-execute rules
    when (go2.val) do
      match (instr2.val) (preExecRules c state)

    -- Pipeline stall
    when (lateWire.val) do
      when ((srcA c (instrData) .==. dst c (instr2.val)) .|.
            (srcB c (instrData) .==. dst c (instr2.val))) do
        stallWire <== true

    -- Latch instruction and PC for next stage
    instr3 <== instr2.val
    pc3 <== pc2.val

    -- Trigger stage 3, except on pipeline flush
    when (pcNext.active.inv) do
      go3 <== go2.val

    -- Pass on RVFI register
    rvfi3 <== rvfi2.val

    -- Stage 3: Execute
    -- ================

    -- State for execute stage
    let state = State {
            opA    = regA.val
          , opB    = regB.val
          , pc     = ReadWrite (pc3.val) (pcNext <==)
          , result = WriteOnly $ \x ->
                       when (dst c (instr3.val) .!=. 0) do
                         resultWire <== x
          , late   = error "Cant write late signal in execute"
          }

    -- Execute rules
    when (go3.val) do
      match (instr3.val) (execRules c state)
      go4 <== go3.val
      -- set RVFI mem info here or in the instruction definitions?

    instr4 <== instr3.val

    -- set RVFI register values
    rvfi4 <== (rvfi3.val) {
        rvfi_rs1_data = regA.val,
        rvfi_rs2_data = regB.val
    }

    -- Stage 4: Writeback
    -- ==================

    -- State for post-execute stage
    let state = State {
            opA    = regA.val.old
          , opB    = regB.val.old
          , pc     = error "Can't access PC in post-execute"
          , result = WriteOnly $ \x ->
                       when (dst c (instr4.val) .!=. 0) do
                         postResultWire <== x
          , late   = error "Can't write late signal in post-execute"
          }

    -- Post-execute rules
    when (go4.val) do
      match (instr4.val) (postExecRules c state)

    -- Determine final result
    let rd = dst c (instr4.val)

    let rvfiRes = if postResultWire.active then postResultWire.val
                                           else resultWire.val.old

    when (postResultWire.active) do
      finalResultWire <== postResultWire.val
    when (postResultWire.active.inv .&. delay 0 (resultWire.active)) do
      finalResultWire <== resultWire.val.old


    -- Writeback
    when (finalResultWire.active) do
      store regFileA rd (finalResultWire.val)
      store regFileB rd (finalResultWire.val)

    -- set RVFI register write value
    rvfifinal <== (rvfi4.val) {
        rvfi_valid = (go4.val.old),
        rvfi_rd_wdata = (rvfiRes)
    }

    display $ rvfifinal.val


  return $ rvfifinal.val
