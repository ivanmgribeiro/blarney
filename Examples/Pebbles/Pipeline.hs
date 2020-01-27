module Pipeline where 
-- 5-stage pipeline for 32-bit 3-operand register-based CPU.

import Blarney
import Blarney.BitScan
import Blarney.Stream

import CHERIBlarneyWrappers

import RVFI_DII

import InstrMem

-- Instructions
--type Instr = Bit 32

-- Register identifiers
type RegId = Bit 5

-- Instruction memory size
--type InstrAddr = Bit 14

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
makeCPUPipeline :: Bool -> Config -> InstrResp -> Module (RVFI_DII_Data, RVFI_DII_InstrReq)
makeCPUPipeline sim c instrResp = do
  -- Instruction memory
  let ext = if sim then ".hex" else ".mif"
  instrMem :: RAM InstrAddr Instr <- makeRAMInit ("prog" ++ ext)

  consume :: Wire (Bit 1) <- makeWire 0

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
  pcNext :: Wire (Bit 93) <- makeWire dontCare

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

  -- Capability program counters for each pipeline stage
  -- TODO optimise by removing unnecessary ones (if pcc permissions/offset/base etc don't
  -- change why store multiple?)
  pcc1 :: Reg (Bit 93) <- makeReg dontCare
  pcc2 :: Reg (Bit 93) <- makeReg dontCare
  pcc3 :: Reg (Bit 93) <- makeReg dontCare
  pcc4 :: Reg (Bit 93) <- makeReg dontCare

  -- Capability SCRs
  ddc :: Reg (Bit 93) <- makeReg 0
  mtcc :: Reg (Bit 93) <- makeReg 0
  mtdc :: Reg (Bit 93) <- makeReg 0
  mscratchc :: Reg (Bit 93) <- makeReg 0
  mepcc :: Reg (Bit 93) <- makeReg 0

  -- signals whether stage 3 has jumped
  jump_wire :: Wire (Bit 1) <- makeWire 0

  -- TODO rename to trapWire to stay in line with RVFI naming?
  exc1_wire :: Wire (Bit 1) <- makeWire 0
  exc1_reg  :: Reg (Bit 1) <- makeReg 0
  exc2_wire :: Wire (Bit 1) <- makeWire 0
  exc2_reg  :: Reg (Bit 1) <- makeReg 0
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
  rvfifinal :: Reg (RVFI_Data) <- makeReg rvfi_base

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

    
    when (regCounter.val .==. 31) do
      started <== 1
      pcc1 <== lower ((almightyCap.setAddr) (0x80000000))
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
      let instrData = instrResp.instrRespValue

      -- consume only when ready to receive an instruction
      consume <== ((instrResp.instrRespValid)
                  .&. (stallWire.val.inv)
                  .&. (exc3_wire.val.inv)
                  .&. (exc4_wire.val.inv)
                  .&. (pcNext.active.inv .|. instrResp.instrRespErr))

      --when (consume.val) do
        --display "consumed instruction 0x" instrData

      --when (consume.val.inv) do
        --display "not consuming"
        --display "instrRespValid: " (instrResp.instrRespValid)
        --display "stallWire: " (stallWire.val)
        --display "exc3_wire: " (exc3_wire.val)
        --display "exc4_wire: " (exc4_wire.val)
        --display "pcNext.active: " (pcNext.active)
        --display "instrRespErr: " (instrResp.instrRespErr)
      --when ((stallWire.val.inv)
      --      .&. (exc3_wire.val.inv)
      --      .&. (exc3_wire.val.inv)
      --      .&. (pcNext.active.inv)) do
      --          consume <== 1

      -- select correct PC to fetch
      let pcFetch = pcNext.active ?
                      (pcNext.val,
                      (stallWire.val .|. instrResp.instrRespValid.inv) ?
                        (pcc1.val,
                         lower ((pcc1.val.setOffset) ((pcc1.val.getOffset) + 4))))

      --display "pcfetch: " pcFetch
      --display "pc1: " (pc1.val)
      --display "pc2: " (pc2.val)pcc1.val
      --display "exc4 " (exc4_wire.val)
      --display "pcNext.active " (pcNext.active)
      --display "pcNext.val " (pcNext.val)
      --display "wrote 0x" (pcFetch) " to pcc1"
      pcc1 <== pcFetch

      -- trigger stage 1 when instruction fetch has returned
      let go1 :: Bit 1 = instrResp.instrRespValid
                         .&. instrResp.instrRespErr.inv

      --display "pcc used for fetch: " pcFetch
      --display "cherichecks: " (cheriInstrChecks (pcFetch))
      --display "pc used for fetch: " (pcFetch.getOffset)

      when (instrResp.instrRespValid .&. instrResp.instrRespErr) do
        --display "instruction check fail"
        pcNext <== mtcc.val
        mepcc <== pcc1.val
        --display "setting mepcc to " (pcc1.val)
        --display "in pc terms " (pcc1.val.getOffset)
        exc1_wire <== 1

      --display "go1: " go1

      -- set RVFI register addresses
      -- hold back the data if stage 1 is being stalled
      rvfi1 <== (rvfi_base) {
              rvfi_pc_rdata = pcFetch.getOffset
          }


      -- Stage 1: Operand Fetch
      -- ======================

      -- Fetch operands
      when (go1 .&. exc1_reg.val.inv .&. exc1_wire.val.inv) do
        load regFileA (srcA c (instrData))
        load regFileB (srcB c (instrData))

      -- Latch instruction and PC for next stage
      instr2 <== instrData
      pcc2 <== pcc1.val
      --display "rvfi1: " (rvfi1.val)
      --display "\n"

      exc2_reg <== if stallWire.val then exc2_reg.val else exc1_wire.val .|. exc1_reg.val


      -- Trigger stage 2, except on pipeline flush or stall
      -- pcNext.active could trigger from stage 1 if the pcc gets set, which would prevent
      -- stage 2 from going ahead even though it should
      let go2_cond = pcNext.active.inv
                     .&. stallWire.val.inv
                     .&. exc1_wire.val.inv
                     .&. exc1_reg.val.inv
                     .&. jump_wire.val.inv

      go2 <== if go1 then go2_cond else 0
      --when go1 do
      --  go2 <== go2_cond

      -- set RVFI register addresses
      -- unset rvfi_valid if the instruction is being stalled
      rvfi2 <== (rvfi1.val) {
              rvfi_valid = instrResp.instrRespValid .&. exc2_wire.val.inv
                                                    .&. exc3_wire.val.inv
                                                    .&. exc4_wire.val.inv
                                                    .&. stallWire.val.inv
                                                    .&. jump_wire.val.inv,
              rvfi_insn = instrData,
              rvfi_rs1_addr = (srcA c (instrData)),
              rvfi_rs2_addr = (srcB c (instrData)),
              rvfi_pc_wdata = pcFetch.getOffset
          }



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


      -- State for pre-execute stage
      let state = State {
              opA       = getAddr a
            , opB       = getAddr b
            , opACap    = a
            , opBCap    = b
            , opAAddr   = (c.srcA) (instr2.val)
            , opBAddr   = (c.srcB) (instr2.val)
            , pc        = ReadWrite (pcc2.val.getOffset) (error "Can't write PC in pre-execute")
            , result    = error "Can't write result in pre-execute"
            , resultCap = error "Can't write resultCap in pre-execute"
            , late      = WriteOnly (lateWire <==)
            , exc       = WriteOnly (exc2_wire <==)
            -- TODO what happens if i set the pcc to something that is unrepresentable
            , pcc       = ReadWrite (pcc2.val) (error "cant write pcc")
            , ddc       = ReadWrite (ddc.val) (error "cant write ddc")
            , mtcc      = ReadWrite (mtcc.val) (mtcc <==)
            , mtdc      = ReadWrite (mtdc.val) (mtdc <==)
            , mscratchc = ReadWrite (mscratchc.val) (mscratchc <==)
            , mepcc     = ReadWrite (mepcc.val) (mepcc <==)
            }

      -- Pre-execute rules
      -- TODO: potential performance improvement: can check for illegal instructions here.
      --       currently only checked in stage 3 for simplicity of exception
      --       implementation
      when (go2.val) do
        match (instr2.val) (preExecRules c state)

      -- Latch operands
      when (go2.val .&. exc2_reg.val.inv .&. exc2_wire.val.inv) do
        regA <== a
        regB <== b

      -- Pipeline stall
      -- stall stage 1 while waiting for the result to come back
      -- TODO optimisation: this stalls unnecessarily when the conflicting address is 0
      --   it also stalls unnecessarily if the 2nd instruction doesnt have an rs2 and has
      --   an immediate instead which happens to coincide with the rs2 of the previous
      --   instruction
      when (lateWire.val) do
        when ((srcA c (instrData) .==. dst c (instr2.val)) .|.
              (srcB c (instrData) .==. dst c (instr2.val))) do
                  stallWire <== true

      -- Latch instruction and PC for next stage
      instr3 <== instr2.val
      pcc3 <== pcc2.val

      -- Trigger stage 3, except on pipeline flush
      when (go2.val) do
        go3 <== pcNext.active.inv
                .&. exc2_wire.val.inv
                .&. exc2_reg.val.inv
                .&. jump_wire.val.inv
      exc3_reg <== exc2_wire.val .|. exc2_reg.val

      --display "rvfi2: " (rvfi2.val)
      --display "\n"

      -- Pass on RVFI register
      rvfi3 <== (rvfi2.val) {
        rvfi_valid = rvfi2.val.rvfi_valid .&. exc3_wire.val.inv
                                          .&. exc4_wire.val.inv
                                          .&. jump_wire.val.inv
                                          -- .&. (stallWire.val.inv) -- don't want this to
                                                                  -- be valid if the
                                                                  -- instruction is being
                                                                  -- stalled
      }


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
            , pc     = ReadWrite (pcc3.val.getOffset)
                                 (\x -> when (exc4_wire.val.inv) do
                                          pcNext <== lower ((pcc3.val.setOffset) x)
                                          jump_wire <== 1)
            , result = WriteOnly $ \x ->
                         when (dst c (instr3.val) .!=. 0) do
                           resultWire <== nullWithAddr x
                           --display "################ writing 0x" x
                           --display "in stage 3"
            , resultCap = WriteOnly $ \x ->
                            when (dst c (instr3.val) .!=. 0) do
                              resultWire <== x
                              --display "result written in stage 3:"
                              --display "  "
                              --        " t:" (x.isValidCap)
                              --        " s:" (x.isSealed)
                              --        " off:" (x.getOffset)
                              --        " top:" (x.getTop)
                              --        " base:" (x.getBase)
                              --        " length: " (x.getLength)
            , late   = error "Cant write late signal in execute"
            , exc    = WriteOnly (exc3_wire <==)
            , pcc       = ReadWrite (pcc3.val)
                                    (\x -> do
                                       pcNext <== x
                                       jump_wire <== 1)
            , ddc       = ReadWrite (ddc.val) (ddc <==)
            , mtcc      = ReadWrite (mtcc.val) (mtcc <==)
            , mtdc      = ReadWrite (mtdc.val) (mtdc <==)
            , mscratchc = ReadWrite (mscratchc.val) (mscratchc <==)
            , mepcc     = ReadWrite (mepcc.val) (mepcc <==)
            }

      -- Execute rules
      -- TODO might not have to check exc3_reg (since it would be taken into account
      -- the previous cycle when setting go3)
      when (go3.val .&. exc4_wire.val.inv .&. exc3_reg.val.inv) do
        matchDefault (instr3.val) (execRules c state) (do exc3_wire <== 1
                                                          pcNext <== mtcc.val
                                                          mepcc <== pcc3.val
                                                          --display "unknown instruction"
                                                      )
        --match (instr3.val) (execRules c state)
        -- set RVFI mem info here or in the instruction definitions?

      instr4 <== instr3.val
      exc4_reg <== (exc3_wire.val) .|. (exc3_reg.val)
      pcc4 <== pcc3.val

      when (go3.val) do
        go4 <== pcNext.active.inv
                .&. exc3_wire.val.inv
                .&. exc3_reg.val.inv

      --display "overwrite pc_wdata? ans: " (pcNext.active)
      --display "rvfi3: " (rvfi3.val)
      --display "\n"

      -- set RVFI register values
      rvfi4 <== (rvfi3.val) {
          rvfi_valid = rvfi3.val.rvfi_valid .&. exc4_wire.val.inv,
          rvfi_rs1_data = regA.val.getAddr,
          rvfi_rs2_data = regB.val.getAddr,
          rvfi_pc_wdata = if (pcNext.active) then pcNext.val.getOffset else rvfi3.val.rvfi_pc_wdata
      }




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
            , pc     = ReadWrite (pcc4.val.getOffset) (\x -> pcNext <== lower ((pcc4.val.setOffset) x))
            , resultCap = WriteOnly $ \x ->
                            when (dst c (instr4.val) .!=. 0) do
                              postResultWire <== x
                              --display "writing in stage 4"
            , result = WriteOnly $ \x ->
                         when (dst c (instr4.val) .!=. 0) do
                           postResultWire <== nullWithAddr x
                           --display "################ writing 0x" x
                           --display "in stage 4"
            , late   = error "Can't write late signal in post-execute"
            , exc    = WriteOnly (exc4_wire <==)
            , pcc       = ReadWrite (pcc4.val)
                                    (\x -> do
                                       pcNext <== x
                                       jump_wire <== 1)
            , ddc       = ReadWrite (ddc.val) (error "cant write ddc")
            , mtcc      = ReadWrite (mtcc.val) (mtcc <==)
            , mtdc      = ReadWrite (mtdc.val) (mtdc <==)
            , mscratchc = ReadWrite (mscratchc.val) (mscratchc <==)
            , mepcc     = ReadWrite (mepcc.val) (mepcc <==)
            }

      -- Post-execute rules
      when (go4.val .&. exc4_reg.val.inv) do
        match (instr4.val) (postExecRules c state)

      -- Determine final result destination
      let rd = if (isCCall (instr4.val)) then 31
                                       else dst c (instr4.val)

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


      -- set RVFI register write value
      rvfifinal <== (rvfi4.val) { rvfi_valid = rvfi4.val.rvfi_valid
                                , rvfi_rd_wdata = (getAddr rvfiRes)
                                , rvfi_trap = (exc4_wire.val .|. exc4_reg.val)
                                , rvfi_pc_wdata = if (exc4_wire.val) then
                                                    pcNext.val.getOffset
                                                  else
                                                    rvfi4.val.rvfi_pc_wdata
                                }

      -- Writeback
      when ((finalResultWire.active) .&. exc4_wire.val.inv .&. (delay 0 (exc4_wire.val.inv))) do
        store regFileA rd (finalResultWire.val)
        store regFileB rd (finalResultWire.val)
        --display "instruction " (instr4.val) " wrote 0x" (finalResultWire.val) " to x" rd
      --display "\n"
      --display "instructions in pipeline: "
      --display "stage 1: " (instrData)
      --        " exc1_reg: " (exc1_reg.val)
      --        " exc1_wire: " (exc1_wire.val)
      --display "stage 2: " (instr2.val)
      --        " exc2_reg: " (exc2_reg.val)
      --        " exc2_wire: " (exc2_wire.val)
      --display "stage 3: " (instr3.val)
      --        " exc3_reg: " (exc3_reg.val)
      --        " exc3_wire: " (exc3_wire.val)
      --display "stage 4: " (instr4.val)
      --        " exc4_reg: " (exc4_reg.val)
      --        " exc4_wire: " (exc4_wire.val)
      --display "stallWire: " (stallWire.val)
      --display "\n"


      ----display "overwrite pc_wdata? ans: " (exc4_wire.val)
      --display "rvfi1: " (rvfi1.val)
      --display "rvfi2: " (rvfi2.val)
      --display "rvfi3: " (rvfi3.val)
      --display "rvfi4: " (rvfi4.val)
      --display "\n"

  return (RVFI_DII_Data { rvfi_data = rvfifinal.val
                        , flush = exc3_wire.val .|. jump_wire.val
                        , flush4 = exc4_wire.val
                        , go4 = go4.val
                        }
         ,RVFI_DII_InstrReq { rvfi_instrReqCap = pcc1.val
                            , rvfi_instrConsume = consume.val
                            }
         )

isCCall :: Bit 32 -> Bit 1
isCCall instr =     ((slice @31 @25 instr) .==. 0x7e)
                .&. ((slice @14 @12 instr) .==. 0x0)
                .&. ((slice @11 @7 instr) .==. 0x01)
                .&. ((slice @6 @0 instr) .==. 0x5b)
