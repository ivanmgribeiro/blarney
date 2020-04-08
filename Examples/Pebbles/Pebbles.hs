module Pebbles where

-- Blarney imports
import Blarney
import Blarney.Queue
import Blarney.Stream
import Blarney.BitScan
import Blarney.Option

-- Pebbles imports
import CSR
import Trap
import DataMem
import Pipeline
import CHERITrap

import InstrMem

-- RVFI imports
import RVFI_DII

import CHERIBlarneyWrappers

-- RISCV I instructions

addi :: State -> Bit 12 -> Action ()
addi s imm = s.result <== s.opA + signExtend imm

slti :: State -> Bit 12 -> Action ()
slti s imm = s.result <== (s.opA `sLT` signExtend imm) ? (1, 0)

sltiu :: State -> Bit 12 -> Action ()
sltiu s imm = s.result <== (s.opA .<. signExtend imm) ? (1, 0)

andi :: State -> Bit 12 -> Action ()
andi s imm = s.result <== s.opA .&. signExtend imm

ori :: State -> Bit 12 -> Action ()
ori s imm = s.result <== s.opA .|. signExtend imm

xori :: State -> Bit 12 -> Action ()
xori s imm = s.result <== s.opA .^. signExtend imm

lui :: State -> Bit 20 -> Action ()
lui s imm = s.result <== signExtend (imm # (0 :: Bit 12))

auipc :: State -> Bit 20 -> Action ()
auipc s imm =
  if s.pcc.val.getFlags then do
    let target = s.pcc.val.getOffset + (imm # (0 :: Bit 12))
    let res = (s.pcc.val.setOffset) target
    if at @93 res then
      s.resultCap <== lower res
    else
      s.resultCap <== nullWithAddr target
  else
    s.result <== s.pc.val + (imm # (0 :: Bit 12))

add :: State -> Action ()
add s = s.result <== s.opA + s.opB

slt :: State -> Action ()
slt s = s.result <== (s.opA `sLT` s.opB) ? (1, 0)

sltu :: State -> Action ()
sltu s = s.result <== (s.opA .<. s.opB) ? (1, 0)

and' :: State -> Action ()
and' s = s.result <== s.opA .&. s.opB

or' :: State -> Action ()
or' s = s.result <== s.opA .|. s.opB

xor :: State -> Action ()
xor s = s.result <== s.opA .^. s.opB

sub :: State -> Action ()
sub s = s.result <== s.opA - s.opB

left :: State -> Bit 5 -> Bit 1 -> Action ()
left s imm reg = do
  let amount = reg ? (slice @4 @0 (s.opB), imm)
  s.result <== s.opA .<<. amount

right :: State -> Bit 1 -> Bit 5 -> Bit 1 -> Action ()
right s arith imm reg = do
  let ext = arith ? (at @31 (s.opA), 0)
  let amount = reg ? (slice @4 @0 (s.opB), imm)
  let value = ext # (s.opA)
  s.result <== truncate (value .>>>. amount)

jal :: State -> Bit 20 -> Action ()
jal s imm = do
  s.pc <== s.pc.val + signExtend (imm # (0 :: Bit 1))
  s.result <== s.pc.val + 4

jalr :: State -> Bit 12 -> Action ()
jalr s imm = do
  s.pc <== truncateLSB (s.opA + signExtend imm) # (0 :: Bit 1)
  s.result <== s.pc.val + 4

beq :: State -> Bit 12 -> Action ()
beq s imm = do
  when (s.opA .==. s.opB) do
    s.pc <== s.pc.val + signExtend (imm # (0 :: Bit 1))

bne :: State -> Bit 12 -> Action ()
bne s imm = do
  when (s.opA .!=. s.opB) do
    s.pc <== s.pc.val + signExtend (imm # (0 :: Bit 1))

blt :: State -> Bit 12 -> Action ()
blt s imm = do
  when (s.opA `sLT` s.opB) do
    s.pc <== s.pc.val + signExtend (imm # (0 :: Bit 1))

bltu :: State -> Bit 12 -> Action ()
bltu s imm = do
  when (s.opA .<. s.opB) do
    s.pc <== s.pc.val + signExtend (imm # (0 :: Bit 1))

bge :: State -> Bit 12 -> Action ()
bge s imm = do
  when (s.opA `sGTE` s.opB) do
    --display "branch target: " (signExtend (imm # (0 :: Bit 1)) :: Bit 32)
    s.pc <== s.pc.val + signExtend (imm # (0 :: Bit 1))

bgeu :: State -> Bit 12 -> Action ()
bgeu s imm = do
  when (s.opA .>=. s.opB) do
    s.pc <== s.pc.val + signExtend (imm # (0 :: Bit 1))

jumpWrap :: State -> CSRUnit -> (State -> Bit m -> Action ()) -> Bit m -> Action ()
jumpWrap s csrUnit jumpInstr = do
  let sModded = (s) {
    pc = ReadWrite (s.pc.val) (\x -> do
                                 let postOffset = (s.pcc.val.setOffset) x
                                 if (at @93 postOffset).inv then
                                   -- TODO it might not always be operand A
                                   cheriTrap True s csrUnit cheri_exc_representabilityViolation (0 # s.opAAddr)
                                 else 
                                   s.pc <== x)
  }
  jumpInstr sModded

--------------------------------------------
-- TODO
-- maybe change these memory operations so that each instruction calls a function
-- in DataMem to do all the stuff it needs to do
-- in particular, the request building could be moved there

memRead_0 :: State -> Action ()
memRead_0 s = s.late <== 1

--memRead_1_old :: State -> DataMem -> CSRUnit -> Bit 12 -> Action ()
--memRead_1_old s mem csrUnit imm =
----  if (((s.opA + signExtend imm) .>=. 0x80000000) .&. ((s.opA + signExtend imm) .<. 0x80010000)
----     .&. (slice @1 @0 (s.opA + signExtend imm) .==. 0)) then
--    dataMemRead mem (s.opA + signExtend imm)
--    --display (slice @1 @0 (s.opA + signExtend imm))
----  else
----    trap s csrUnit (Exception exc_loadAccessFault)
--
--memRead_2_old :: State -> DataMem -> CSRUnit -> Bit 12 -> Bit 1 -> Bit 2 -> Action ()
--memRead_2_old s mem csrUnit imm unsigned width =
--  --display "read memory value: " $ readMux mem (s.opA + signExtend imm) width unsigned
--  --case res of
--  --  (Left memData) -> s.result <== memData
--  --  (Right resp) -> do
--  --    trap s csrUnit (Exception exc_loadAccessFault)
--  --    display "tried to read memory out of bounds"
--  --where res = readMux mem (s.opA + signExtend imm) width unsigned
--  s.result <== 0 # (readMux mem (s.opA + signExtend imm) width unsigned)

memRead_1 :: State -> MemIn -> CSRUnit -> Bit 12 -> Bit 2 -> Action ()
memRead_1 s memIn csrUnit imm width = do
  --display "memRead_1"
  let authCap = if s.pcc.val.getFlags then s.opACap else s.ddc.val
  let addrOffset = if s.pcc.val.getFlags then 0 else s.opA
  memIn <== MemReq {
    memReqCap = authCap
  , memReqAddr = authCap.getAddr + signExtend imm + addrOffset
  , memReqWrite = 0
  , memReqWidth = width
  , memReqValue = 0
  , memReqTag = 0
  }


memRead_2 :: State -> MemResp -> CSRUnit -> Bit 12 -> Bit 1 -> Bit 2 -> Action ()
memRead_2 s memResp csrUnit imm unsigned width = do
  --display "memRead_2"
  if (memResp.memRespErr.inv) then do
    if (width .==. 3) then
      s.resultCap <== fromMem (memResp.memRespTag # memResp.memRespValue)
    else do
      let res :: Bit 32 = lower (memResp.memRespValue)
      let resSigned = if (width .==. 2) then
                        res
                      else if (width .==. 1) then
                        if unsigned then res else signExtend (slice @15 @0 res)
                      else
                        if unsigned then res else signExtend (slice @7 @0 res)
      s.result <== resSigned
  else
    trap s csrUnit (Exception exc_loadAccessFault)

memRead_2_wrap :: Stream (Bit 8)
                  -> MemIn
                  -> State
                  -> MemResp
                  -> CSRUnit
                  -> Bit 12
                  -> Bit 1
                  -> Bit 2
                  -> Action ()
memRead_2_wrap uartIn memIn s resp csrUnit imm unsigned width = do
  if memIn.val.old.memReqAddr .==. 0xC01DF01D then
    s.result <== zeroExtend (uartIn.canPeek)
  else if memIn.val.old.memReqAddr .==. 0xC01DF02D then do
    s.result <== zeroExtend (uartIn.peek)
    display "value in core: " (uartIn.peek)
    uartIn.consume
  else
    memRead_2 s resp csrUnit imm unsigned width

cMemRead_0 :: State -> Action ()
cMemRead_0 s = s.late <== 1

cMemRead_1 :: State -> MemIn -> Bit 1 -> Bit 2 -> Action ()
cMemRead_1 s memIn ddcRelative width = do
  -- ddcRelative = 0 means instruction is ddc-relative
  --display "cMemRead_1"
  let addr = if ddcRelative.inv then s.ddc.val.getAddr + s.opA else s.opACap.getAddr
  let authCap = if ddcRelative.inv then s.ddc.val else s.opACap
  memIn <== MemReq {
    memReqCap = authCap
  , memReqAddr = addr
  , memReqWrite = 0
  , memReqWidth = lower width
  , memReqValue = 0
  , memReqTag = 0
  }

cMemRead_2 :: State -> MemResp -> CSRUnit -> Bit 1 -> Bit 2 -> Action ()
cMemRead_2 s memResp csrUnit unsigned width = do
  --display "cMemRead2"
  if (memResp.memRespErr.inv) then do
    if (width .==. 3) then
      s.resultCap <== fromMem (memResp.memRespTag # memResp.memRespValue)
    else do
      let res :: Bit 32 = lower (memResp.memRespValue)
      let resSigned = if (width .==. 2) then
                        res
                      else if (width .==. 1) then
                        if unsigned then res else signExtend (slice @15 @0 res)
                      else
                        if unsigned then res else signExtend (slice @7 @0 res)
      s.result <== resSigned
  else
    -- TODO set the cause and address of this exception properly
    cheriTrap False s csrUnit (cheri_exc_permitLoadViolation) (0 # s.opAAddr)


--memWrite_old :: State -> DataMem -> CSRUnit -> Bit 12 -> Bit 2 -> Action ()
--memWrite_old s mem csrUnit imm width = do
--  if ((s.opA + signExtend imm .>=. 0x80000000) .&. (s.opA + signExtend imm .<. 0x80010000)
--    .&. (slice @1 @0 (s.opA + signExtend imm) .==. 0)) then
--    dataMemWrite mem width (s.opA + signExtend imm) (s.opB)
--  else
--    trap s csrUnit (Exception exc_storeAMOAccessFault)

memWrite_1 :: State -> MemIn -> CSRUnit -> Bit 12 -> Bit 2 -> Action ()
memWrite_1 s memIn csrUnit imm width = do
  --display "memWrite_1"
  let authCap = if s.pcc.val.getFlags then s.opACap else s.ddc.val
  let addrOffset = if s.pcc.val.getFlags then 0 else s.opA
  let writeData = if width .==. 3 then toMem (s.opBCap) else zeroExtend (s.opB)
  memIn <== MemReq {
    memReqCap = authCap
  , memReqAddr = authCap.getAddr + signExtend imm + addrOffset
  , memReqWrite = 1
  , memReqWidth = width
  , memReqValue = lower writeData
  , memReqTag = upper writeData
  }

memWrite_2 :: State -> MemResp -> CSRUnit -> Action ()
memWrite_2 s memResp csrUnit = do
  --display "memWrite_2"
  when (memResp.memRespErr) do
    trap s csrUnit (Exception exc_storeAMOAccessFault)


cMemWrite_1 :: State -> MemIn -> Bit 1 -> Bit 2 -> Action ()
cMemWrite_1 s memIn ddcRelative width = do
  -- ddcRelative = 0 means instruction is ddc-relative
  --display "cMemWrite_1"
  let addr = if ddcRelative.inv then s.ddc.val.getAddr + s.opA else s.opACap.getAddr
  let authCap = if ddcRelative.inv then s.ddc.val else s.opACap
  let writeData = if width .==. 3 then toMem (s.opBCap) else zeroExtend (s.opB)
  memIn <== MemReq {
    memReqCap = authCap
  , memReqAddr = addr
  , memReqWrite = 1
  , memReqWidth = lower width
  , memReqValue = lower writeData
  , memReqTag = upper writeData
  }

cMemWrite_2 :: State -> MemResp -> CSRUnit -> Action ()
cMemWrite_2 s memResp csrUnit = do
  --display "cMemWrite_2"
  when (memResp.memRespErr) do
    -- TODO set the cause and address of this exception properly
    cheriTrap False s csrUnit (cheri_exc_permitStoreViolation) (0 # s.opAAddr)

--cMemWrite_2 :: State -> MemIn -> CSRUnit -> Bit 3 -> Bit 1 -> Action ()
--cMemWrite s memIn csrUnit width ddcRelative

fence :: State -> Bit 4 -> Bit 4 -> Bit 4 -> Action ()
fence s fm pred succ = display "fence not implemented"

ecall :: State -> CSRUnit -> Action ()
ecall s csrUnit = trap s csrUnit (Exception exc_eCallFromM)

ebreak :: State -> CSRUnit -> Action ()
ebreak s csrUnit = trap s csrUnit (Exception exc_breakpoint)

mret :: State -> CSRUnit -> Action ()
mret s csrUnit = s.pc <== s.mepcc.val.getOffset

csrrw :: State -> CSRUnit -> Bit 12 -> Action ()
csrrw s csrUnit csr = do
  -- Simple treatment of CSRs for now
  if (csr .!=. 0xBC0) then do
    readCSR csrUnit csr (s.result)
    writeCSR csrUnit csr (s.opA)
  else do
    s.result <== zeroExtend (s.mccsr.val)
    s.mccsr <== lower (s.opA)

csrrs :: State -> CSRUnit -> Bit 12 -> Action ()
csrrs s csrUnit csr = do
  if (csr .!=. 0xBC0) then do
    readCSR csrUnit csr (s.result)
    when (s.opAAddr .!=. 0) do
      setHighCSR csrUnit csr (s.opA)
  else do
    s.result <== zeroExtend (s.mccsr.val)
    when (s.opAAddr .!=. 0) do
      s.mccsr <== s.mccsr.val .|. lower (s.opA)

csrrc :: State -> CSRUnit -> Bit 12 -> Action ()
csrrc s csrUnit csr = do
  if (csr .!=. 0xBC0) then do
    readCSR csrUnit csr (s.result)
    when (s.opAAddr .!=. 0) do
      clearHighCSR csrUnit csr (s.opA)
  else do
    s.result <== zeroExtend (s.mccsr.val)
    when (s.opAAddr .!=. 0) do
      s.mccsr <== s.mccsr.val .&. lower (s.opA.inv)

csrrwi :: State -> CSRUnit -> Bit 12 -> Bit 5 -> Action ()
csrrwi s csrUnit csr imm = do
  if (csr .!=. 0xBC0) then do
    readCSR csrUnit csr (s.result)
    writeCSR csrUnit csr (zeroExtend imm)
  else do
    s.result <== zeroExtend (s.mccsr.val)
    s.mccsr <== zeroExtend imm

csrrsi :: State -> CSRUnit -> Bit 12 -> Bit 5 -> Action ()
csrrsi s csrUnit csr imm = do
  if (csr .!=. 0xBC0) then do
    readCSR csrUnit csr (s.result)
    when (imm .!=. 0) do
      setHighCSR csrUnit csr (zeroExtend imm)
  else do
    s.result <== zeroExtend (s.mccsr.val)
    when (imm .!=. 0) do
      s.mccsr <== s.mccsr.val .|. zeroExtend imm

csrrci :: State -> CSRUnit -> Bit 12 -> Bit 5 -> Action ()
csrrci s csrUnit csr imm = do
  if (csr .!=. 0xBC0) then do
    readCSR csrUnit csr (s.result)
    when (imm .!=. 0) do
      clearHighCSR csrUnit csr (zeroExtend imm)
  else do
    s.result <== zeroExtend (s.mccsr.val)
    when (imm .!=. 0) do
      s.mccsr <== s.mccsr.val .&. (zeroExtend imm).inv

cGetPerms :: State -> Action ()
cGetPerms s = do
  --display "cGetPerms"
  s.result <== zeroExtend (s.opACap.getPerms)

cGetType   :: State -> Action ()
cGetType s = do
  --display "cGetType"
  let res = s.opACap.getType
  let resExtend = if res .>=. 12 then signExtend res else zeroExtend res
  ----display $ res
  s.result <== resExtend

cGetBase   :: State -> Action ()
cGetBase s = do
  --display "cGetBase"
  s.result <== s.opACap.getBase

cGetLen    :: State -> Action ()
cGetLen s = do
  --display "cGetLen"
  let len = s.opACap.getLength
  s.result <== if at @32 len then inv 0 else lower len

cGetTag    :: State -> Action ()
cGetTag s = do
  --display "cGetTag"
  s.result <== zeroExtend (s.opACap.isValidCap)

cGetSealed :: State -> Action ()
cGetSealed s = do
  --display "cGetSealed"
  s.result <== zeroExtend (s.opACap.isSealed)

cGetOffset :: State -> Action ()
cGetOffset s = do
  --display "cGetOffset"
  s.result <== s.opACap.getOffset

cGetFlags  :: State -> Action ()
cGetFlags s = do
  --display "cGetFlags"
  s.result <== zeroExtend (s.opACap.getFlags)

cGetAddr   :: State -> Action ()
cGetAddr s = do
  --display "cGetAddr"
  s.result <== s.opACap.getAddr

cSeal           :: State -> CSRUnit -> Action ()
cSeal s csrUnit = do
  --display "cSeal"
  let newCap = (s.opACap.setType) (lower (s.opBCap.getAddr))
  if s.opACap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if s.opBCap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opBAddr)
  else if s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else if s.opBCap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opBAddr)
  -- TODO make this 7 a constant elsewhere
  else if (at @7 (s.opBCap.getPerms)).inv then
    cheriTrap True s csrUnit cheri_exc_permitSealViolation (0 # s.opBAddr)
  else if s.opBCap.getAddr .<. s.opBCap.getBase then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opBAddr)
  else if zeroExtend (s.opBCap.getAddr) .>=. s.opBCap.getTop then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opBAddr)
  -- TODO this might be the wrong max OTYPE
  else if s.opBCap.getAddr .>=. 0xc then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opBAddr)
  -- TODO RVBS and the sail definitions have a representability check here
  -- does this need it as well? the wrapper only has 93 bits
  else
    s.resultCap <== newCap



cUnseal         :: State -> CSRUnit -> Action ()
cUnseal s csrUnit = do
  --display "cUnseal"
  if s.opACap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if s.opBCap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opBAddr)
  else if s.opACap.isSealed.inv then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else if s.opBCap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opBAddr)
  else if s.opBCap.getAddr .!=. zeroExtend (s.opACap.getType) then
    cheriTrap True s csrUnit cheri_exc_typeViolation (0 # s.opBAddr)
  -- TODO replace this with a constant
  else if (at @10 (s.opBCap.getPerms)).inv then
    cheriTrap True s csrUnit cheri_exc_unsealViolation (0 # s.opBAddr)
  else if s.opBCap.getAddr .<. s.opBCap.getBase then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opBAddr)
  else if zeroExtend (s.opBCap.getAddr) .>=. s.opBCap.getTop then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opBAddr)
  else do
    let newCap = slice @92 @0 ((s.opACap.setType) (-1))
    let oldPerms = newCap.getPerms
    -- TODO set global perm
    let newCapWithPerms = (newCap.setPerms) (oldPerms)
    s.resultCap <== newCapWithPerms


cAndPerm        :: State -> CSRUnit -> Action ()
cAndPerm s csrUnit = do
  --display "cAndPerm"
  if s.opACap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else
    s.resultCap <== (s.opACap.setPerms) (s.opACap.getPerms .&. lower (s.opB))

cSetFlags       :: State -> CSRUnit -> Action ()
cSetFlags s csrUnit = do
  --display "cSetFlags"
  if s.opACap.isValidCap .&. s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else
    s.resultCap <== (s.opACap.setFlags) (lower (s.opB))

cSetOffset      :: State -> CSRUnit -> Action ()
cSetOffset s csrUnit = do
  --display "cSetOffset"
  if s.opACap.isValidCap .&. s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else do
    let res = (s.opACap.setOffset) (s.opB)
    s.resultCap <== if at @93 res then lower res else nullWithAddr (s.opACap.getBase + s.opB)

cSetAddr        :: State -> CSRUnit -> Action ()
cSetAddr s csrUnit = do
  --display "cSetAddr"
  if s.opACap.isValidCap .&. s.opACap.isSealed then do
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else do
    let res = (s.opACap.setAddr) (s.opB)
    s.resultCap <== if at @93 res then lower res else nullWithAddr (s.opB)

cIncOffset      :: State -> CSRUnit -> Action ()
cIncOffset s csrUnit = do
  --display "cIncOffset"
  if s.opACap.isValidCap .&. s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else do
    let res = (s.opACap.setOffset) (s.opACap.getOffset + s.opB)
    s.resultCap <== if at @93 res then lower res else nullWithAddr (s.opACap.getAddr + s.opB)


cIncOffsetImm   :: State -> CSRUnit -> Bit 12 -> Action ()
cIncOffsetImm s csrUnit imm = do
  --display "cIncOffsetImm"
  if s.opACap.isValidCap .&. s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else do
    let res = (s.opACap.setOffset) (s.opACap.getOffset + signExtend imm)
    s.resultCap <== if at @93 res then lower res else nullWithAddr (s.opACap.getAddr + signExtend imm)


cSetBounds      :: State -> CSRUnit -> Action ()
cSetBounds s csrUnit = do
  --display "cSetBounds"
  if s.opACap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else if s.opACap.getAddr .<. s.opACap.getBase then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else if zeroExtend (s.opACap.getAddr) + zeroExtend (s.opB) .>. s.opACap.getTop then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else
    s.resultCap <== lower ((s.opACap.setBounds) (s.opB))

cSetBoundsExact :: State -> CSRUnit -> Action ()
cSetBoundsExact s csrUnit = do
  --display "cSetBoundsExact"
  let newCap = (s.opACap.setBounds) (s.opB)
  if s.opACap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else if s.opACap.getAddr .<. s.opACap.getBase then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else if zeroExtend (s.opACap.getAddr) + zeroExtend (s.opB) .>. s.opACap.getTop then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else if inv (at @93 newCap) then
    -- TODO check if this if should be inverted
    cheriTrap True s csrUnit cheri_exc_representabilityViolation (0 # s.opAAddr)
  else
    s.resultCap <== lower (newCap)

cSetBoundsImm   :: State -> CSRUnit -> Bit 12 -> Action ()
cSetBoundsImm s csrUnit imm = do
  --display "cSetBoundsImm"
  let newCap = (s.opACap.setBounds) (zeroExtend imm)
  if s.opACap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else if s.opACap.getAddr .<. s.opACap.getBase then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else if zeroExtend (s.opACap.getAddr) + zeroExtend imm .>. s.opACap.getTop then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else
    s.resultCap <== lower (newCap)

cClearTag       :: State -> Action ()
cClearTag s = do
  --display "cClearTag"
  s.resultCap <== (s.opACap.setValidCap) 0

cBuildCap       :: State -> CSRUnit -> Action ()
cBuildCap s csrUnit = do
  --display "cBuildCap"
  let aDDC = if s.opAAddr .==. 0 then s.ddc.val else s.opACap
  --display "input cap a: " (aDDC)
  --display "input cap b: " (s.opBCap)
  --display "valid: " (aDDC.isValidCap)
  if (aDDC.isValidCap).inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if aDDC.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else if s.opBCap.getBase .<. aDDC.getBase then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else if s.opBCap.getTop .>. aDDC.getTop then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else if zeroExtend (s.opBCap.getBase) .>. s.opBCap.getTop  then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opBAddr)
  else if (aDDC.getPerms .&. s.opBCap.getPerms) .!=. s.opBCap.getPerms then
    cheriTrap True s csrUnit cheri_exc_softDefPermViolation (0 # s.opAAddr)
  else do
    -- TODO check this implementation
    -- it seems all 4 sources disagree - ibex, sail, rvbs, piccolo
    -- for now, implemented to agree with ibex
    let resType = (s.opBCap.setType) (aDDC.getType)
    let resValid = (resType.setValidCap) 1
    s.resultCap <== resValid

cCopyType       :: State -> CSRUnit -> Action ()
cCopyType s csrUnit = do
  --display "cCopyType"
  if s.opACap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else if s.opBCap.isSealed then
    if zeroExtend (s.opBCap.getType) .<. s.opACap.getBase then
      cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
    else if zeroExtend (s.opBCap.getType) .>=. s.opACap.getTop then
      cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
    else
      s.resultCap <== lower ((s.opACap.setOffset) (zeroExtend (zeroExtend (s.opBCap.getType) - (s.opACap.getBase))))
  else
    s.result <== -1

cCSeal           :: State -> CSRUnit -> Action ()
cCSeal s csrUnit = do
  --display "cCSeal"
  let newCap = (s.opACap.setType) (lower (s.opBCap.getAddr))
  if s.opACap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if s.opBCap.isValidCap.inv then
    s.resultCap <== s.opACap
  else if s.opBCap.getAddr .==. -1 then
    s.resultCap <== s.opACap
  else if s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else if s.opBCap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opBAddr)
  -- TODO make this 7 a constant elsewhere
  else if (at @7 (s.opBCap.getPerms)).inv then
    cheriTrap True s csrUnit cheri_exc_permitSealViolation (0 # s.opBAddr)
  else if s.opBCap.getAddr .<. s.opBCap.getBase then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opBAddr)
  else if zeroExtend (s.opBCap.getAddr) .>=. s.opBCap.getTop then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opBAddr)
  else if s.opBCap.getAddr .>=. 0xc then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opBAddr)
  -- TODO RVBS and the sail definitions have a representability check here
  -- does this need it as well? the wrapper only has 93 bits
  else
    s.resultCap <== newCap


cToPtr   :: State -> CSRUnit -> Action ()
cToPtr s csrUnit = do
  --display "cToPtr"
  let bDDC = if s.opBAddr .==. 0 then s.ddc.val else s.opBCap
  if bDDC.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opBAddr)
  else if s.opACap.isValidCap .&. s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else
    s.result <== if s.opACap.isValidCap.inv then 0 else (s.opACap.getAddr - bDDC.getBase)


cFromPtr :: State -> CSRUnit -> Action ()
cFromPtr s csrUnit = do
  --display "cFromPtr"
  let aDDC = if s.opAAddr .==. 0 then s.ddc.val else s.opACap
  if s.opB .==. 0 then
    s.resultCap <== nullCap
  else if aDDC.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if aDDC.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else do
    let res = (aDDC.setOffset) (s.opB)
    -- TODO replace 93 with a constant
    if at @93 res then
      s.resultCap <== lower res
    else
      s.resultCap <== nullWithAddr (aDDC.getBase + s.opB)





cSub     :: State -> Action ()
cSub s = do
  --display "cSub"
  s.result <== (s.opACap.getAddr) - (s.opBCap.getAddr)

cMove    :: State -> Action ()
cMove s = do
  --display "cMove"
  s.resultCap <== s.opACap

-- TODO check that target address is aligned properly
-- (can't have 2-byte aligned instructions)
cJALR :: State -> CSRUnit -> Action ()
cJALR s csrUnit = do
  if s.opACap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if s.opACap.isSealed then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  -- TODO replace this with a constant
  else if (at @1 (s.opACap.getPerms)).inv then
    cheriTrap True s csrUnit cheri_exc_permitExecuteViolation (0 # s.opAAddr)
  else if s.opACap.getAddr .<. s.opACap.getBase then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else if zeroExtend (s.opACap.getAddr + 4) .>. s.opACap.getTop then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else do
    let res = (s.pcc.val.setOffset) (s.pcc.val.getOffset + 4)
    if (at @93 res).inv then
      cheriTrap True s csrUnit cheri_exc_representabilityViolation (0 # s.opAAddr)
    else do
      s.resultCap <== lower res
      s.pcc <== lower ((s.opACap.setOffset) (slice @31 @1 (s.opACap.getOffset) # 0))

-- TODO check that target address is aligned properly
-- (can't have 2-byte aligned instructions)
cCall :: State -> CSRUnit -> Action ()
cCall s csrUnit = do
  --display "cCall"
  let newPC = s.opACap.getAddr
  if s.opACap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opAAddr)
  else if s.opBCap.isValidCap.inv then
    cheriTrap True s csrUnit cheri_exc_tagViolation (0 # s.opBAddr)
  else if s.opACap.isSealed.inv then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else if s.opBCap.isSealed.inv then
    cheriTrap True s csrUnit cheri_exc_sealViolation (0 # s.opAAddr)
  else if s.opACap.getType .!=. s.opBCap.getType then
    cheriTrap True s csrUnit cheri_exc_typeViolation (0 # s.opAAddr)
  -- TODO replace these with constants
  else if (at @8 (s.opACap.getPerms)).inv then
    cheriTrap True s csrUnit cheri_exc_permitCCallViolation (0 # s.opAAddr)
  else if (at @8 (s.opBCap.getPerms)).inv then
    cheriTrap True s csrUnit cheri_exc_permitCCallViolation (0 # s.opBAddr)
  else if (at @1 (s.opACap.getPerms)).inv then
    cheriTrap True s csrUnit cheri_exc_permitExecuteViolation (0 # s.opAAddr)
  else if at @1 (s.opBCap.getPerms) then
    cheriTrap True s csrUnit cheri_exc_permitExecuteViolation (0 # s.opBAddr)
  else if newPC .<. s.opACap.getBase then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else if zeroExtend (newPC + 4) .>. s.opACap.getTop then
    cheriTrap True s csrUnit cheri_exc_lengthViolation (0 # s.opAAddr)
  else do
    let res = (((s.opACap.setType) (-1)).setOffset) ((slice @31 @1 (s.opACap.getOffset)) # 0)
    if (at @93 res).inv then
      cheriTrap True s csrUnit cheri_exc_representabilityViolation (0 # s.opAAddr)
    else do
      s.resultCap <== (s.opBCap.setType) (-1)
      s.pcc <== lower res

cTestSubset :: State -> Action ()
cTestSubset s = do
  let aDDC = if s.opAAddr .==. 0 then s.ddc.val else s.opACap
  --display "cTestSubset"
  s.result <== if aDDC.isValidCap .!=. s.opBCap.isValidCap then
                 0
               else if s.opBCap.getBase .<. aDDC.getBase then
                 0
               else if s.opBCap.getTop .>. aDDC.getTop then
                 0
               else if (aDDC.getPerms .&. s.opBCap.getPerms) .!=. s.opBCap.getPerms then
                 0
               else
                 1

-- TODO rewrite cSpecialRW in a cleaner way?
-- probably easier to clean up if the SCRs are not special-cased and are put
-- into their own file?
cSpecialRW :: State -> CSRUnit -> Bit 5 -> Action ()
cSpecialRW s csrUnit id = do
  --display "cSpecialRW"
  if id .==. 0 then -- PCC
    if s.opAAddr .!=. 0 then
      -- trying to write to pcc with csprw - illegal
      cheriTrap True s csrUnit cheri_exc_accessSysRegsViolation (1 # id)
    else
      s.resultCap <== s.pcc.val
  else if id .==. 1 then do -- DDC
    s.resultCap <== s.ddc.val
    when (s.opAAddr .!=. 0) do
      s.ddc <== s.opACap
  -- TODO replace this @10 with a constant somewhere
  else if (at @10 (s.pcc.val.getPerms)).inv then
    cheriTrap True s csrUnit cheri_exc_accessSysRegsViolation (1 # id)
  -- MTCC
  else if id .==. 28 then do
      s.resultCap <== s.mtcc.val
      when (s.opAAddr .!=. 0) do
        if s.opACap.isSealed then do
          s.mtcc <== nullWithAddr ((slice @31 @2 (s.opACap.getAddr)) # 0)
          csrUnit.mtvec <== (slice @31 @2 (s.opACap.getOffset)) # 0
        else do
          -- TODO ask about this. can this ever make mtcc non-exact?
          -- and if so, what do we do?
          let offset = s.opACap.getOffset
          s.mtcc <== lower ((s.opACap.setOffset) ((slice @31 @2 offset) # 0))
          csrUnit.mtvec <== slice @31 @2 offset # 0
          --s.mtcc <== s.opACap
          --csrUnit.mtvec <== s.opACap.getOffset
        -- TODO mtvec should probably be written elsewhere
  -- MTDC
  else if id .==. 29 then do
      s.resultCap <== s.mtdc.val
      when (s.opAAddr .!=. 0) do
        s.mtdc <== s.opACap
  -- MSCRATCHC
  else if id .==. 30 then do
      --display "writing back " (s.mscratchc.val) " with addr " (s.mscratchc.val.getAddr)
      s.resultCap <== s.mscratchc.val
      when (s.opAAddr .!=. 0) do
        --display "writing mscratchc with " (s.opACap) " with addr " (s.opACap.getAddr)
        s.mscratchc <== s.opACap
  -- MEPCC
  else if id .==. 31 then do
      --display "reading mepcc returned " (s.mepcc.val)
      --display "in pcc terms: " (s.mepcc.val.getOffset)
      s.resultCap <== s.mepcc.val
      when (s.opAAddr .!=. 0) do
        --display "setting mepcc to " (s.opACap)
        --display "in pcc terms " (s.opACap.getOffset)
        if s.opACap.isSealed then do
          s.mepcc <== nullWithAddr ((slice @31 @2 (s.opACap.getAddr)) # 0)
          csrUnit.mepc <== (slice @31 @2 (s.opACap.getOffset)) # 0
        else do
          let res = (s.opACap.setOffset) ((slice @31 @1 (s.opACap.getOffset)) # 0)
          if at @93 res then do
            s.mepcc <== lower res
            csrUnit.mepc <== (slice @31 @1 (s.opACap.getOffset)) # 0
          else
            display "mepcc was made inexact - this shouldn't happen"
  else do
    --display "tried to write to a SCR that doesn't exist"
    trap s csrUnit (Exception exc_illegalInstr)
    --cheriTrap True s csrUnit cheri_exc_setCIDViolation (1 # id)

mul :: State -> Action ()
mul s = do
  s.result <== s.opA .*. s.opB
--
--mul_1 :: State -> Action ()
--mul_1 s = do
--  s.

  -- valid ids: 0  - pcc
  --            1  - ddc
  --            28 - mtcc
  --            29 - mtdc
  --            30 - mscratchc
  --            31 - mepcc

--cRoundRepresentableLength :: State -> Action()
--cRepresentableAlignmentMask :: State -> Action ()

-- RV32I CPU, with UART input and output channels
makePebbles :: Bool -> Bool -> RVFI_DII_In -> Module (RVFI_DII_Out)
makePebbles sim dii dii_in = do
  -- TODO can i replace this with a . operator?
  let insnIn = insnInput dii_in
  let uartIn = uartInput dii_in

  memInput :: MemIn <- makeWire MemReq {
    memReqCap = 0
  , memReqAddr = 0
  , memReqWrite = 0
  , memReqWidth = 0
  , memReqValue = 0
  , memReqTag = 0
  }

  memOutput <- makeDataMemCore sim True memInput

  instrInput :: InstrIn <- makeWire InstrReq {
    instrReqCap = 0
  , instrWrite = 0
  , instrWriteCap = 0
  , instrWriteAddr = 0
  , instrWriteWidth = 0
  , instrWriteData = 0
  , instrWriteTag = 0
  }

  instrOutput <- makeInstrMem sim dii instrInput dii_in

  -- CSR unit
  (uartOut, csrUnit) <- makeCSRUnit uartIn

  -- Execute rules
  let execute s =
        [ "imm[11:0] <5> 000 <5> 0010011" ==> addi s
        , "imm[11:0] <5> 010 <5> 0010011" ==> slti s
        , "imm[11:0] <5> 011 <5> 0010011" ==> sltiu s
        , "imm[11:0] <5> 111 <5> 0010011" ==> andi s
        , "imm[11:0] <5> 110 <5> 0010011" ==> ori s
        , "imm[11:0] <5> 100 <5> 0010011" ==> xori s
        , "imm[19:0] <5> 0110111" ==> lui s
        , "imm[19:0] <5> 0010111" ==> auipc s
        , "0000000 <5> <5> 000 <5> 0110011" ==> add s
        , "0000000 <5> <5> 010 <5> 0110011" ==> slt s
        , "0000000 <5> <5> 011 <5> 0110011" ==> sltu s
        , "0000000 <5> <5> 111 <5> 0110011" ==> and' s
        , "0000000 <5> <5> 110 <5> 0110011" ==> or' s
        , "0000000 <5> <5> 100 <5> 0110011" ==> xor s
        , "0100000 <5> <5> 000 <5> 0110011" ==> sub s
        , "0000000 imm[4:0] <5> 001 <5> 0 reg<1> 10011" ==> left s
        , "0 arith<1> 00000 imm[4:0] <5> 101 <5> 0 reg<1> 10011" ==> right s
        , "imm[19] imm[9:0] imm[10] imm[18:11] <5> 1101111" ==> jumpWrap s csrUnit jal
        , "imm[11:0] <5> 000 <5> 1100111" ==> jumpWrap s csrUnit jalr
        , "imm[11] imm[9:4] <5> <5> 000 imm[3:0] imm[10] 1100011" ==> jumpWrap s csrUnit beq
        , "imm[11] imm[9:4] <5> <5> 001 imm[3:0] imm[10] 1100011" ==> jumpWrap s csrUnit bne
        , "imm[11] imm[9:4] <5> <5> 100 imm[3:0] imm[10] 1100011" ==> jumpWrap s csrUnit blt
        , "imm[11] imm[9:4] <5> <5> 110 imm[3:0] imm[10] 1100011" ==> jumpWrap s csrUnit bltu
        , "imm[11] imm[9:4] <5> <5> 101 imm[3:0] imm[10] 1100011" ==> jumpWrap s csrUnit bge
        , "imm[11] imm[9:4] <5> <5> 111 imm[3:0] imm[10] 1100011" ==> jumpWrap s csrUnit bgeu
        , "imm[11:0] <5> <1> w<2> <5> 0000011" ==> memRead_1 s memInput csrUnit
        , "imm[11:5] <5> <5> 0 w<2> imm[4:0] 0100011" ==> memWrite_1 s memInput csrUnit
        , "fm[3:0] pred[3:0] succ[3:0] <5> 000 <5> 0001111" ==> fence s
        , "000000000000 <5> 000 <5> 1110011" ==> ecall s csrUnit
        , "000000000001 <5> 000 <5> 1110011" ==> ebreak s csrUnit
        , "001100000010 00000 000 00000 1 1100 11" ==> mret s csrUnit
        , "csr<12> <5> 001 <5> 1110011" ==> csrrw s csrUnit
        , "csr<12> <5> 010 <5> 1110011" ==> csrrs s csrUnit
        , "csr<12> <5> 011 <5> 1110011" ==> csrrc s csrUnit
        , "csr<12> imm<5> 101 <5> 1110011" ==> csrrwi s csrUnit
        , "csr<12> imm<5> 110 <5> 1110011" ==> csrrsi s csrUnit
        , "csr<12> imm<5> 111 <5> 1110011" ==> csrrci s csrUnit
        , "0000001 <5> <5> 000 <5> 0110011" ==> mul s
        ]

  let cheriExecute s = (execute s) ++
        [ "1111111 00000 <5> 000 <5> 1011011" ==> cGetPerms s
        , "1111111 00001 <5> 000 <5> 1011011" ==> cGetType s
        , "1111111 00010 <5> 000 <5> 1011011" ==> cGetBase s
        , "1111111 00011 <5> 000 <5> 1011011" ==> cGetLen s
        , "1111111 00100 <5> 000 <5> 1011011" ==> cGetTag s
        , "1111111 00101 <5> 000 <5> 1011011" ==> cGetSealed s
        , "1111111 00110 <5> 000 <5> 1011011" ==> cGetOffset s
        , "1111111 00111 <5> 000 <5> 1011011" ==> cGetFlags s
        , "1111111 01111 <5> 000 <5> 1011011" ==> cGetAddr s

        , "0001011 <5> <5> 000 <5> 1011011" ==> cSeal s csrUnit
        , "0001100 <5> <5> 000 <5> 1011011" ==> cUnseal s csrUnit
        , "0001101 <5> <5> 000 <5> 1011011" ==> cAndPerm s csrUnit
        , "0001110 <5> <5> 000 <5> 1011011" ==> cSetFlags s csrUnit
        , "0001111 <5> <5> 000 <5> 1011011" ==> cSetOffset s csrUnit
        , "0010000 <5> <5> 000 <5> 1011011" ==> cSetAddr s csrUnit
        , "0010001 <5> <5> 000 <5> 1011011" ==> cIncOffset s csrUnit

        , "imm[11:0] <5> 001 <5> 1011011" ==> cIncOffsetImm s csrUnit
        , "0001000 <5> <5> 000 <5> 1011011" ==> cSetBounds s csrUnit
        , "0001001 <5> <5> 000 <5> 1011011" ==> cSetBoundsExact s csrUnit
        , "imm[11:0] <5> 010 <5> 1011011" ==> cSetBoundsImm s csrUnit
        , "1111111 01011 <5> 000 <5> 1011011" ==> cClearTag s
        , "0011101 <5> <5> 000 <5> 1011011" ==> cBuildCap s csrUnit
        , "0011110 <5> <5> 000 <5> 1011011" ==> cCopyType s csrUnit
        , "0011111 <5> <5> 000 <5> 1011011" ==> cCSeal s csrUnit

        , "0010010 <5> <5> 000 <5> 1011011" ==> cToPtr s csrUnit
        , "0010011 <5> <5> 000 <5> 1011011" ==> cFromPtr s csrUnit
        , "0010100 <5> <5> 000 <5> 1011011" ==> cSub s
        , "1111111 01010 <5> 000 <5> 1011011" ==> cMove s

        , "1111111 01100 <5> 000 <5> 1011011" ==> cJALR s csrUnit
        , "1111110 <5> <5> 000 <5> 1011011" ==> cCall s csrUnit
        , "0100000 <5> <5> 000 <5> 1011011" ==> cTestSubset s
        , "0000001 id[4:0] <5> 000 <5> 1011011" ==> cSpecialRW s csrUnit

        , "1111101 0 ddc<1> <1> w<2> <5> 000 <5> 1011011" ==> cMemRead_1 s memInput
        , "1111100 <5> <5> 000 0 ddc<1> 0 w<2> 1011011" ==> cMemWrite_1 s memInput
        --, "1111111 01000 <5> 000 <5> 1011011" ==> cRoundRepresentableLength s
        --, "1111111 01001 <5> 000 <5> 1011011" ==> cRepresentableAlignmentMask s
         ]

  -- Pre-execute rules
  let preExecute s =
        [ "<12> <5> <3> <5> 0000011" ==> memRead_0 s
        , "1111101 0 <4> <5> 000 <5> 1011011" ==> cMemRead_0 s
        ]

  -- Post-execute rules
  let postExecute s =
        [ "imm[11:0] <5> u<1> w<2> <5> 0000011" ==> memRead_2_wrap uartIn memInput s memOutput csrUnit
        , "1111101 0 <1> u<1> w<2> <5> 000 <5> 1011011 " ==> cMemRead_2 s memOutput csrUnit
        , "<7> <5> <5> 0 <2> <5> 0100011" ==> memWrite_2 s memOutput csrUnit
        , "1111100 <5> <5> 000 0 <1> 0 <2> 1011011" ==> cMemWrite_2 s memOutput csrUnit
        ]

  -- CPU pipeline
  (rvfi_dii_data, dii_instrReq) <- makeCPUPipeline sim
                                   (Config { srcA = slice @19 @15
                                   ,         srcB = slice @24 @20
                                   ,         dst  = slice @11 @7
                                   ,         preExecRules = preExecute
                                   ,         execRules = cheriExecute
                                   ,         postExecRules = postExecute
                                   })
                                   instrOutput

  -- TODO see if there is a more natural place/way to do this
  let req_old = memInput.val.old.old
  let active_old = memInput.active.old.old
  let rvfi_data_with_mem = (rvfi_dii_data.rvfi_data) {
      rvfi_mem_addr  = req_old.memReqAddr
                       .&. signExtend (active_old)
    , rvfi_mem_rdata = memOutput.old.memRespValue
                       .&. signExtend (active_old)
    , rvfi_mem_wdata = req_old.memReqValue
                       .&. signExtend (active_old)
    , rvfi_mem_rmask = widthToBE (req_old.memReqWidth)
                       .&. signExtend (active_old
                                       .&. req_old.memReqWrite.inv)
    , rvfi_mem_wmask = widthToBE (req_old.memReqWidth)
                       .&. signExtend (active_old
                                       .&. req_old.memReqWrite)
    }


  always do
    -- pass consume signal to dii stream
    instrInput <== InstrReq { instrReqCap = dii_instrReq.rvfi_instrReqCap
                            , instrWrite = memInput.val.memReqWrite
                            , instrWriteCap = memInput.val.memReqCap
                            , instrWriteAddr = memInput.val.memReqAddr
                            , instrWriteData = memInput.val.memReqValue
                            , instrWriteWidth = memInput.val.memReqWidth
                            , instrWriteTag = memInput.val.memReqTag
                            }
    when (dii_instrReq.rvfi_instrConsume) do
      --display "consuming " (dii_instrReq.rvfi_instrReqCap.getAddr)
      insnIn.consume

  return $ RVFI_DII_Out { uart_output = uartOut
                        , rvfi_dii_data = rvfi_dii_data {
                            rvfi_data = rvfi_data_with_mem
                            }
                        , rvfi_dii_consume = dii_instrReq.rvfi_instrConsume
                        }

widthToBE :: Bit 2 -> Bit 8
widthToBE w =
  if w .==. 0 then 0x1
  else if w .==. 1 then 0x3
  else if w .==. 2 then 0xF
  else 0xFF
