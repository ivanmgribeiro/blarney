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
auipc s imm = s.result <== s.pc.val + (imm # (0 :: Bit 12))

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
    s.pc <== s.pc.val + signExtend (imm # (0 :: Bit 1))

bgeu :: State -> Bit 12 -> Action ()
bgeu s imm = do
  when (s.opA .>=. s.opB) do
    s.pc <== s.pc.val + signExtend (imm # (0 :: Bit 1))


--------------------------------------------
-- TODO
-- maybe change these memory operations so that each instruction calls a function
-- in DataMem to do all the stuff it needs to do
-- in particular, the request building could be moved there

memRead_0 :: State -> Action ()
memRead_0 s = s.late <== 1

memRead_1_old :: State -> DataMem -> CSRUnit -> Bit 12 -> Action ()
memRead_1_old s mem csrUnit imm =
--  if (((s.opA + signExtend imm) .>=. 0x80000000) .&. ((s.opA + signExtend imm) .<. 0x80010000)
--     .&. (slice @1 @0 (s.opA + signExtend imm) .==. 0)) then
    dataMemRead mem (s.opA + signExtend imm)
    --display (slice @1 @0 (s.opA + signExtend imm))
--  else
--    trap s csrUnit (Exception exc_loadAccessFault)

memRead_2_old :: State -> DataMem -> CSRUnit -> Bit 12 -> Bit 1 -> Bit 2 -> Action ()
memRead_2_old s mem csrUnit imm unsigned width =
  --display "read memory value: " $ readMux mem (s.opA + signExtend imm) width unsigned
  --case res of
  --  (Left memData) -> s.result <== memData
  --  (Right resp) -> do
  --    trap s csrUnit (Exception exc_loadAccessFault)
  --    display "tried to read memory out of bounds"
  --where res = readMux mem (s.opA + signExtend imm) width unsigned
  s.result <== 0 # (readMux mem (s.opA + signExtend imm) width unsigned)

memRead_1 :: State -> MemIn -> CSRUnit -> Bit 12 -> Bit 2 -> Action ()
memRead_1 s memIn csrUnit imm width = do
  memIn <== MemReq {
    memReqAddr = s.opA + signExtend imm
  , memReqWrite = 0
  , memReqWidth = width
  , memReqValue = 0
  }

memRead_2 :: State -> MemResp -> CSRUnit -> Bit 12 -> Bit 1 -> Bit 2 -> Action ()
memRead_2 s memResp csrUnit imm unsigned width =
  if (isSome (memResp.memRespValue)) then do
    let res = memResp.memRespValue.val
    let resSigned = if (width .==. 2) then
                      res
                    else if (width .==. 1) then
                      if unsigned then res else signExtend (slice @15 @0 res)
                    else
                      if unsigned then res else signExtend (slice @7 @0 res)
    s.result <== resSigned
  else
    trap s csrUnit (Exception exc_loadAccessFault)

memWrite_old :: State -> DataMem -> CSRUnit -> Bit 12 -> Bit 2 -> Action ()
memWrite_old s mem csrUnit imm width = do
  if ((s.opA + signExtend imm .>=. 0x80000000) .&. (s.opA + signExtend imm .<. 0x80010000)
    .&. (slice @1 @0 (s.opA + signExtend imm) .==. 0)) then
    dataMemWrite mem width (s.opA + signExtend imm) (s.opB)
  else
    trap s csrUnit (Exception exc_storeAMOAccessFault)

memWrite_1 :: State -> MemIn -> CSRUnit -> Bit 12 -> Bit 2 -> Action ()
memWrite_1 s memIn csrUnit imm width = do
  memIn <== MemReq {
    memReqAddr = s.opA + signExtend imm
  , memReqWrite = 1
  , memReqWidth = width
  , memReqValue = s.opB
  }

memWrite_2 :: State -> MemResp -> CSRUnit -> Action ()
memWrite_2 s memResp csrUnit = do
  when (isNone (memResp.memRespValue)) do
    trap s csrUnit (Exception exc_storeAMOAccessFault)

fence :: State -> Bit 4 -> Bit 4 -> Bit 4 -> Action ()
fence s fm pred succ = display "fence not implemented"

ecall :: State -> CSRUnit -> Action ()
ecall s csrUnit = trap s csrUnit (Exception exc_eCallFromU)

ebreak :: State -> CSRUnit -> Action ()
ebreak s csrUnit = trap s csrUnit (Exception exc_breakpoint)

csrrw :: State -> CSRUnit -> Bit 12 -> Action ()
csrrw s csrUnit csr = do
  -- Simple treatment of CSRs for now
  readCSR csrUnit csr (s.result)
  writeCSR csrUnit csr (s.opA)

cGetPerms :: State -> Action ()
cGetPerms s = do
  display "cGetPerms"
  s.result <== zeroExtend (s.opACap.getPerms)

cGetType   :: State -> Action ()
cGetType s = do
  display "cGetType"
  let res = s.opACap.getType
  let resExtend = if res .>=. 12 then signExtend res else zeroExtend res
  --display $ res
  s.result <== resExtend

cGetBase   :: State -> Action ()
cGetBase s = do
  display "cGetBase"
  s.result <== s.opACap.getBase

cGetLen    :: State -> Action ()
cGetLen s = do
  display "cGetLen"
  let len = s.opACap.getLength
  s.result <== if index @32 len then inv 0 else lower len

cGetTag    :: State -> Action ()
cGetTag s = do
  display "cGetTag"
  s.result <== zeroExtend (s.opACap.isValidCap)

cGetSealed :: State -> Action ()
cGetSealed s = do
  display "cGetSealed"
  s.result <== zeroExtend (s.opACap.isSealed)

cGetOffset :: State -> Action ()
cGetOffset s = do
  display "cGetOffset"
  s.result <== s.opACap.getOffset

cGetFlags  :: State -> Action ()
cGetFlags s = do
  display "cGetFlags"
  s.result <== zeroExtend (s.opACap.getFlags)

cGetAddr   :: State -> Action ()
cGetAddr s = do
  display "cGetAddr"
  s.result <== s.opACap.getAddr

cSeal           :: State -> CSRUnit -> Action ()
cSeal s csrUnit = do
  display "cSeal"
  let newCap = (s.opACap.setType) (lower (s.opBCap.getAddr))
  if s.opACap.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opBCap.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else if s.opBCap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  -- TODO make this 7 a constant elsewhere
  else if (index @7 (s.opBCap.getPerms)).inv then
    cheriTrap s csrUnit cheri_exc_permitSealViolation
  else if s.opBCap.getAddr .<. s.opBCap.getBase then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if zeroExtend (s.opBCap.getAddr) .>=. s.opBCap.getTop then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if s.opBCap.getAddr .>=. 0xc then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  -- TODO RVBS and the sail definitions have a representability check here
  -- does this need it as well? the wrapper only has 93 bits
  else
    s.resultCap <== newCap



cUnseal         :: State -> CSRUnit -> Action ()
cUnseal s csrUnit = do
  display "cUnseal"
  if s.opACap.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opBCap.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opACap.isSealed.inv then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else if s.opBCap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else if s.opBCap.getAddr .!=. zeroExtend (s.opACap.getType) then
    cheriTrap s csrUnit cheri_exc_typeViolation
  -- TODO replace this with a constant
  else if (index @10 (s.opBCap.getPerms)).inv then
    cheriTrap s csrUnit cheri_exc_unsealViolation
  else if s.opBCap.getAddr .<. s.opBCap.getBase then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if zeroExtend (s.opBCap.getAddr) .>=. s.opBCap.getTop then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else do
    let newCap = range @92 @0 ((s.opACap.setType) (-1))
    let oldPerms = newCap.getPerms
    -- TODO set global perm
    let newCapWithPerms = (newCap.setPerms) (oldPerms)
    s.resultCap <== newCapWithPerms


cAndPerm        :: State -> CSRUnit -> Action ()
cAndPerm s csrUnit = do
  display "cAndPerm"
  if s.opACap.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else
    s.resultCap <== (s.opACap.setPerms) (s.opACap.getPerms .&. lower (s.opB))

cSetFlags       :: State -> CSRUnit -> Action ()
cSetFlags s csrUnit = do
  display "cSetFlags"
  if s.opACap.isValidCap .&. s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else
    s.resultCap <== (s.opACap.setFlags) (lower (s.opB))

cSetOffset      :: State -> CSRUnit -> Action ()
cSetOffset s csrUnit = do
  display "cSetOffset"
  if s.opACap.isValidCap .&. s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else do
    let res = (s.opACap.setOffset) (s.opB)
    s.resultCap <== if index @93 res then lower res else nullWithAddr (s.opACap.getBase + s.opB)

cSetAddr        :: State -> CSRUnit -> Action ()
cSetAddr s csrUnit = do
  display "cSetAddr"
  if s.opACap.isValidCap .&. s.opACap.isSealed then do
    cheriTrap s csrUnit cheri_exc_sealViolation
  else do
    let res = (s.opACap.setAddr) (s.opB)
    s.resultCap <== if index @93 res then lower res else nullWithAddr (s.opB)

cIncOffset      :: State -> CSRUnit -> Action ()
cIncOffset s csrUnit = do
  display "cIncOffset"
  if s.opACap.isValidCap .&. s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else do
    let res = (s.opACap.setOffset) (s.opACap.getOffset + s.opB)
    s.resultCap <== if index @93 res then lower res else nullWithAddr (s.opACap.getAddr + s.opB)


cIncOffsetImm   :: State -> CSRUnit -> Bit 12 -> Action ()
cIncOffsetImm s csrUnit imm = do
  display "cIncOffsetImm"
  if s.opACap.isValidCap .&. s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else do
    let res = (s.opACap.setOffset) (s.opACap.getOffset + signExtend imm)
    s.resultCap <== if index @93 res then lower res else nullWithAddr (s.opACap.getAddr + signExtend imm)


cSetBounds      :: State -> CSRUnit -> Action ()
cSetBounds s csrUnit = do
  display "cSetBounds"
  if s.opACap.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else if s.opACap.getAddr .<. s.opACap.getBase then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if zeroExtend (s.opACap.getAddr) + zeroExtend (s.opB) .>. s.opACap.getTop then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else
    s.resultCap <== lower ((s.opACap.setBounds) (s.opB))

cSetBoundsExact :: State -> CSRUnit -> Action ()
cSetBoundsExact s csrUnit = do
  display "cSetBoundsExact"
  let newCap = (s.opACap.setBounds) (s.opB)
  if s.opACap.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else if s.opACap.getAddr .<. s.opACap.getBase then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if zeroExtend (s.opACap.getAddr) + zeroExtend (s.opB) .>. s.opACap.getTop then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if inv (index @93 newCap) then
    -- TODO check if this if should be inverted
    cheriTrap s csrUnit cheri_exc_representabilityViolation
  else
    s.resultCap <== lower (newCap)

cSetBoundsImm   :: State -> CSRUnit -> Bit 12 -> Action ()
cSetBoundsImm s csrUnit imm = do
  display "cSetBoundsImm"
  let newCap = (s.opACap.setBounds) (zeroExtend imm)
  if s.opACap.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else if s.opACap.getAddr .<. s.opACap.getBase then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if zeroExtend (s.opACap.getAddr) + zeroExtend imm .>. s.opACap.getTop then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else
    s.resultCap <== lower (newCap)

cClearTag       :: State -> Action ()
cClearTag s = do
  display "cClearTag"
  s.resultCap <== (s.opACap.setValidCap) 0

cBuildCap       :: State -> CSRUnit -> Action ()
cBuildCap s csrUnit = do
  display "cBuildCap"
  let aDDC = if s.opAAddr .==. 0 then s.ddc.val else s.opACap
  display "valid: " (aDDC.isValidCap)
  -- TODO make this use DDC when op A is register 0
  if (aDDC.isValidCap).inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if aDDC.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else if s.opBCap.getBase .<. aDDC.getBase then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if s.opBCap.getTop .>. aDDC.getTop then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if zeroExtend (s.opBCap.getBase) .>. s.opBCap.getTop  then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if (aDDC.getPerms .&. s.opBCap.getPerms) .!=. s.opBCap.getPerms then
    cheriTrap s csrUnit cheri_exc_softDefPermViolation
  else do
    -- TODO check this implementation
    -- it seems all 4 sources disagree - ibex, sail, rvbs, piccolo
    -- for now, implemented to agree with ibex
    let resType = (s.opBCap.setType) (aDDC.getType)
    let resValid = (resType.setValidCap) 1
    s.resultCap <== resValid

cCopyType       :: State -> CSRUnit -> Action ()
cCopyType s csrUnit = do
  display "cCopyType"
  if s.opACap.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else if s.opBCap.isSealed then
    if zeroExtend (s.opBCap.getType) .<. s.opACap.getBase then
      cheriTrap s csrUnit cheri_exc_lengthViolation
    else if zeroExtend (s.opBCap.getType) .>=. s.opACap.getTop then
      cheriTrap s csrUnit cheri_exc_lengthViolation
    else
      s.resultCap <== lower ((s.opACap.setOffset) (zeroExtend (zeroExtend (s.opBCap.getType) - (s.opACap.getBase))))
  else
    s.result <== -1

cCSeal           :: State -> CSRUnit -> Action ()
cCSeal s csrUnit = do
  display "cCSeal"
  let newCap = (s.opACap.setType) (lower (s.opBCap.getAddr))
  if s.opACap.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opBCap.isValidCap.inv then
    s.resultCap <== s.opACap
  else if s.opBCap.getAddr .==. -1 then
    s.resultCap <== s.opACap
  else if s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else if s.opBCap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  -- TODO make this 7 a constant elsewhere
  else if (index @7 (s.opBCap.getPerms)).inv then
    cheriTrap s csrUnit cheri_exc_permitSealViolation
  else if s.opBCap.getAddr .<. s.opBCap.getBase then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if zeroExtend (s.opBCap.getAddr) .>=. s.opBCap.getTop then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  else if s.opBCap.getAddr .>=. 0xc then
    cheriTrap s csrUnit cheri_exc_lengthViolation
  -- TODO RVBS and the sail definitions have a representability check here
  -- does this need it as well? the wrapper only has 93 bits
  else
    s.resultCap <== newCap


cToPtr   :: State -> CSRUnit -> Action ()
cToPtr s csrUnit = do
  display "cToPtr"
  let bDDC = if s.opBAddr .==. 0 then s.ddc.val else s.opBCap
  if bDDC.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if s.opACap.isValidCap .&. s.opACap.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else
    s.result <== if s.opACap.isValidCap.inv then 0 else (s.opACap.getAddr - bDDC.getBase)


cFromPtr :: State -> CSRUnit -> Action ()
cFromPtr s csrUnit = do
  display "cFromPtr"
  let aDDC = if s.opAAddr .==. 0 then s.ddc.val else s.opACap
  if s.opB .==. 0 then
    s.resultCap <== nullCap
  else if aDDC.isValidCap.inv then
    cheriTrap s csrUnit cheri_exc_tagViolation
  else if aDDC.isSealed then
    cheriTrap s csrUnit cheri_exc_sealViolation
  else do
    let res = (aDDC.setOffset) (s.opB)
    -- TODO replace 93 with a constant
    if index @93 res then
      s.resultCap <== lower res
    else
      s.resultCap <== nullWithAddr (aDDC.getBase + s.opB)





cSub     :: State -> Action ()
cSub s = do
  display "cSub"
  s.result <== (s.opACap.getAddr) - (s.opBCap.getAddr)

cMove    :: State -> Action ()
cMove s = do
  display "cMove"
  s.resultCap <== s.opACap

--cJALR :: State -> CSRUnit -> Action ()
--cCall :: State -> CSRUnit -> Action ()

cTestSubset :: State -> Action ()
cTestSubset s = do
  let aDDC = if s.opAAddr .==. 0 then s.ddc.val else s.opACap
  display "cTestSubset"
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
  display "cSpecialRW"
  if id .==. 0 then -- PCC
    if s.opAAddr .!=. 0 then
      -- trying to write to pcc with csprw - illegal
      cheriTrap s csrUnit cheri_exc_accessSysRegsViolation
    else
      s.resultCap <== s.pcc.val
  else if id .==. 1 then do -- DDC
    s.resultCap <== s.ddc.val
    when (s.opAAddr .!=. 0) do
      s.ddc <== s.opACap
  -- MTCC
  else if id .==. 28 then
    -- TODO replace 11 with a constant
    if (index @11 (s.pcc.val.getPerms)).inv then
      cheriTrap s csrUnit cheri_exc_accessSysRegsViolation
    else do
      s.resultCap <== s.mtcc.val
      when (s.opAAddr .!=. 0) do
        s.mtcc <== s.opACap
        -- TODO mtvec should probably be written elsewhere
        csrUnit.mtvec <== s.opACap.getAddr
  -- MTDC
  else if id .==. 29 then
    if (index @11 (s.pcc.val.getPerms)).inv then
      cheriTrap s csrUnit cheri_exc_accessSysRegsViolation
    else do
      s.resultCap <== s.mtdc.val
      when (s.opAAddr .!=. 0) do
        s.mtdc <== s.opACap
  -- MSCRATCHC
  else if id .==. 30 then
    if (index @11 (s.pcc.val.getPerms)).inv then
      cheriTrap s csrUnit cheri_exc_accessSysRegsViolation
    else do
      s.resultCap <== s.mscratchc.val
      when (s.opAAddr .!=. 0) do
        s.mscratchc <== s.opACap
  -- MEPCC
  else if id .==. 31 then
    if (index @11 (s.pcc.val.getPerms)).inv then
      cheriTrap s csrUnit cheri_exc_accessSysRegsViolation
    else do
      s.resultCap <== s.mepcc.val
      when (s.opAAddr .!=. 0) do
        s.mepcc <== s.opACap
        csrUnit.mepc <== s.opACap.getAddr
  else
    cheriTrap s csrUnit cheri_exc_setCIDViolation




  -- valid ids: 0  - pcc
  --            1  - ddc
  --            28 - mtcc
  --            29 - mtdc
  --            30 - mscratchc
  --            31 - mepcc


--cRoundRepresentableLength :: State -> Action()
--cRepresentableAlignmentMask :: State -> Action ()

-- RV32I CPU, with UART input and output channels
makePebbles :: Bool -> RVFI_DII_In -> Module (RVFI_DII_Out)
makePebbles sim dii_in = do
  -- TODO can i replace this with a . operator?
  let insnIn = insnInput dii_in
  let uartIn = uartInput dii_in

  memInput :: Wire (MemReq) <- makeWire MemReq {
    memReqAddr = 0
  , memReqWrite = 0
  , memReqWidth = 0
  , memReqValue = 0
  }

  memOutput <- makeDataMemCore sim memInput

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
        , "imm[19] imm[9:0] imm[10] imm[18:11] <5> 1101111" ==> jal s
        , "imm[11:0] <5> 000 <5> 1100111" ==> jalr s
        , "imm[11] imm[9:4] <5> <5> 000 imm[3:0] imm[10] 1100011" ==> beq s
        , "imm[11] imm[9:4] <5> <5> 001 imm[3:0] imm[10] 1100011" ==> bne s
        , "imm[11] imm[9:4] <5> <5> 100 imm[3:0] imm[10] 1100011" ==> blt s
        , "imm[11] imm[9:4] <5> <5> 110 imm[3:0] imm[10] 1100011" ==> bltu s
        , "imm[11] imm[9:4] <5> <5> 101 imm[3:0] imm[10] 1100011" ==> bge s
        , "imm[11] imm[9:4] <5> <5> 111 imm[3:0] imm[10] 1100011" ==> bgeu s
        , "imm[11:0] <5> <1> w<2> <5> 0000011" ==> memRead_1 s memInput csrUnit
        , "imm[11:5] <5> <5> 0 w<2> imm[4:0] 0100011" ==> memWrite_1 s memInput csrUnit
        , "fm[3:0] pred[3:0] succ[3:0] <5> 000 <5> 0001111" ==> fence s
        , "000000000000 <5> 000 <5> 1110011" ==> ecall s csrUnit
        , "000000000001 <5> 000 <5> 1110011" ==> ebreak s csrUnit
        , "csr<12> <5> 001 <5> 1110011" ==> csrrw s csrUnit
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
        , "0011111 01010 <5> 000 <5> 1011011" ==> cMove s

        --, "1111111 01100 <5> 000 <5> 1011011" ==> cJALR s
        --, "1111110 <5> <5> 000 <5> 1011011" ==> cCall s
        , "0100000 <5> <5> 000 <5> 1011011" ==> cTestSubset s
        , "0000001 id[4:0] <5> 000 <5> 1011011" ==> cSpecialRW s csrUnit
        --, "1111111 01000 <5> 000 <5> 1011011" ==> cRoundRepresentableLength s
        --, "1111111 01001 <5> 000 <5> 1011011" ==> cRepresentableAlignmentMask s
         ]

  -- Pre-execute rules
  let preExecute s =
        [ "<12> <5> <3> <5> 0000011" ==> memRead_0 s
        ]

  -- Post-execute rules
  let postExecute s =
        [ "imm[11:0] <5> u<1> w<2> <5> 0000011" ==> memRead_2 s memOutput csrUnit
        , "<7> <5> <5> 0 <2> <5> 0100011" ==> memWrite_2 s memOutput csrUnit
        ]

  -- CPU pipeline
  rvfi_dii_data <- makeCPUPipeline sim
                                   (Config { srcA = slice @19 @15
                                           , srcB = slice @24 @20
                                           , dst  = slice @11 @7
                                           , preExecRules = preExecute
                                           , execRules = cheriExecute
                                           , postExecRules = postExecute })
                                   insnIn

  return $ RVFI_DII_Out {uart_output = uartOut, rvfi_dii_data = rvfi_dii_data}
