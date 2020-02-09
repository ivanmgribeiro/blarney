-- 32-bit wide tightly-coupled data memory
module DataMem where

import Blarney
import Blarney.Core.RAM
import Blarney.Option

import CHERIBlarneyWrappers

-- Data memory size in bytes
type LogDataMemSize = 23

-- memory base & size constants
-- TODO make LogDataMemSize depend on these
memBase = 0xC0000000
memSize = 0x18BCB0

-- Implement data memory as eight block RAMs
-- (one for each byte of double word)
type DataMem = [RAM (Bit (LogDataMemSize-3)) (Bit 8)]

-- Implement tag memory as a single block ram containing 1 bit per address
type TagMem = RAM (Bit (LogDataMemSize)) (Bit 1)

-- RV32I memory access width
type AccessWidth = Bit 2

-- the memReqCap is used ONLY for providing authorization
data MemReq = MemReq {
  memReqCap :: Bit 93,
  memReqAddr :: Bit 32,
  memReqWrite :: Bit 1,
  memReqWidth :: AccessWidth,
  memReqValue :: Bit 64,
  memReqTag :: Bit 1
} deriving (Generic, Bits, FShow)

data MemResp = MemResp {
  memRespValue :: Bit 64,
  memRespTag :: Bit 1,
  memRespErr :: Bit 1,
  memRespErrCode :: Bit 6
} deriving (Generic, Bits)

type MemIn = Wire MemReq

-- TODO extend this to take in the memory base & size
makeDataMemCore :: Bool -> Bool -> MemIn -> Module MemResp
makeDataMemCore sim printStuff memIn = do
  dataMem :: DataMem <- makeDataMemInit sim
  tagMem :: TagMem <- makeRAM

  -- information about the pending request
  -- TODO might make more sense to just make a Reg (MemReq) to hold this,
  -- or to use old
  readPending :: Reg (Bit 1) <- makeReg 0
  readPendingAddr :: Reg (Bit 32) <- makeReg 0
  readPendingWidth :: Reg (AccessWidth) <- makeReg dontCare
  readPendingAlignment :: Reg (Bit 3) <- makeReg dontCare
  errPending :: Reg (Bit 1) <- makeDReg 0

  -- TODO this probably shouldn't be a wire
  responseData :: Wire (Bit 64) <- makeWire 0
  responseTag :: Wire (Bit 1) <- makeWire 0

  always do
    let addrBottom = slice @2 @0 (memIn.val.memReqAddr)
    -- check if the address is unaligned with respect to the memory access width
    let isUnaligned = if isDoubleAccess (memIn.val.memReqWidth) then
                        addrBottom .!=. 0
                      else if isWordAccess (memIn.val.memReqWidth) then
                        slice @1 @0 addrBottom .!=. 0
                      else if isHalfAccess (memIn.val.memReqWidth) then
                        at @0 (addrBottom) .!=. 0
                      else
                        0
    let size = zeroExtend (accessWidthToSize (memIn.val.memReqWidth))

    when (memIn.active) do
      --when ((memIn.val.memReqAddr .>=. memBase + memSize)
      --      .|. (memIn.val.memReqAddr .<=. memBase)) do
      --  when (memIn.val.memReqWrite) do
      --    display "wrote special addr 0x" (memIn.val.memReqAddr)
      --    display (lower (memIn.val.memReqValue) :: Bit 8)
      --  when (memIn.val.memReqWrite.inv) do
      --    display "read special addr 0x" (memIn.val.memReqAddr)
      if printStuff then do
        when (memIn.val.memReqAddr .==. 0xC01DF00D) do
          when (memIn.val.memReqWrite) do
            display_ "%c" (lower (memIn.val.memReqValue) :: Bit 8)
      else noAction


    ------------------------------

    ----      READ LOGIC      ----

    ------------------------------

    -- read logic part 1
    -- test if memory address is valid and if it is, set the proper
    -- inputs to load the data
    -- if not, don't request anything and (memIn.val.memReqAddr)trigger an error
    readPending <== memIn.active .&. memIn.val.memReqWrite.inv
    readPendingAddr <== memIn.val.memReqAddr
    readPendingWidth <== memIn.val.memReqWidth
    readPendingAlignment <== addrBottom

    when (memIn.active .&. memIn.val.memReqWrite.inv) do
      --display "memory read addr: " (memIn.val.memReqAddr)
      if ((memIn.val.memReqAddr .>=. memBase)
         .&. (memIn.val.memReqAddr .<=. memBase + memSize - size)
         .&. (isUnaligned.inv)
         .&. (cheriLoadChecks (memIn.val.memReqCap)
                                  (memIn.val.memReqAddr)
                                  (memIn.val.memReqWidth) .==. 0)) then do
        dataMemRead dataMem (memIn.val.memReqAddr)
        when (isDoubleAccess (memIn.val.memReqWidth)) do
          let tagMemAddr = lower (upper (memIn.val.memReqAddr) :: Bit 29)
          load tagMem tagMemAddr
      else do
        --display "errored read, memchecks: " (cheriLoadChecks (memIn.val.memReqCap)
        --                                                     (memIn.val.memReqAddr)
        --                                                     (memIn.val.memReqWidth))
        --display "checkTop: " (memIn.val.memReqAddr .>=. memBase)
        --display "checkBase: " (memIn.val.memReqAddr .<. memBase + memSize)
        --display "isUnaligned: " (isUnaligned)
        --display "cap top: " (memIn.val.memReqCap.getTop)
        --display "cap base: " (memIn.val.memReqCap.getBase)
        --display "cap valid: " (memIn.val.memReqCap.isValidCap)
        --display "cap isSealed: " (memIn.val.memReqCap.isSealed)
        --display "cap getPerms: " (memIn.val.memReqCap.getPerms)
        when ((memIn.val.memReqAddr .!=. 0xC01DF00D)
              .&. (memIn.val.memReqAddr .!=. 0xC01DF01D)
              .&. (memIn.val.memReqAddr .!=. 0xC01DF02D)) do
          --display "read failed addr " (memIn.val.memReqAddr)
          --display "cheri checks: "(cheriLoadChecks (memIn.val.memReqCap)
          --                                         (memIn.val.memReqAddr)
          --                                         (memIn.val.memReqWidth))
          errPending <== 1

    -- read logic part 2
    -- get the memory values that were read and set the response signals
    when (readPending.val) do
      if (readPendingAddr.val .==. 0xC01DF01D) then do
        --display "reading c01df01d"
        responseData <== 0x0
        responseTag <== 0
      else do
        responseData <== readMux dataMem
                                 (0 # readPendingAlignment.val)
                                 (readPendingWidth.val)
                                 1
        responseTag <== out tagMem
        --display "read succeeded at " (readPendingAddr.val) ", data: " (responseData.val)

    -------------------------------

    ----      WRITE LOGIC      ----

    -------------------------------

    -- write logic
    -- test if memory address is valid and if it is, set the proper
    -- inputs to store the data
    -- if not, don't request anything and trigger an error
    when (memIn.active .&. memIn.val.memReqWrite) do
      if ((memIn.val.memReqAddr .>=. memBase)
         .&. (memIn.val.memReqAddr .<=. memBase + memSize - size)
         .&. (isUnaligned.inv)
         .&. (cheriStoreChecks (memIn.val.memReqCap)
                                   (memIn.val.memReqAddr)
                                   (memIn.val.memReqWidth) .==. 0)) then do
        dataMemWrite dataMem
                     (memIn.val.memReqWidth)
                     (memIn.val.memReqAddr)
                     (memIn.val.memReqValue)
        when (isDoubleAccess (memIn.val.memReqWidth)) do
          let tagMemAddr = lower (upper (memIn.val.memReqAddr) :: Bit 29)
          store tagMem tagMemAddr (memIn.val.memReqTag)
        --display "write succeeded " (memIn.val)
      else do
        --display "errored write, memchecks: " (cheriStoreChecks (memIn.val.memReqCap)
        --                                                       (memIn.val.memReqAddr)
        --                                                       (memIn.val.memReqWidth))
        --display "checkTop: " (memIn.val.memReqAddr .>=. memBase)
        --display "checkBase: " (memIn.val.memReqAddr .<. memBase + memSize)
        --display "isUnaligned: " (isUnaligned)
        --display "cap top: " (memIn.val.memReqCap.getTop)
        --display "cap base: " (memIn.val.memReqCap.getBase)
        --display "cap valid: " (memIn.val.memReqCap.isValidCap)
        --display "cap isSealed: " (memIn.val.memReqCap.isSealed)
        --display "cap getPerms: " (memIn.val.memReqCap.getPerms)
        when ((memIn.val.memReqAddr .!=. 0xC01DF00D)
              .&. (memIn.val.memReqAddr .!=. 0xC01DF01D)
              .&. (memIn.val.memReqAddr .!=. 0xC01DF02D)) do
          --display "write failed at addr" (memIn.val.memReqAddr)
          --display "cheri checks: "(cheriStoreChecks (memIn.val.memReqCap)
          --                                         (memIn.val.memReqAddr)
          --                                         (memIn.val.memReqWidth))
          errPending <== 1


  return MemResp {
    memRespValue = errPending.val ? (0, responseData.val),
    memRespTag = responseTag.val,
    memRespErr = errPending.val,
    memRespErrCode = 1
  }


-- Constructor
makeDataMem :: Bool -> Module DataMem
makeDataMem sim =
    sequence [makeRAM | i <- [0..7]]
  where ext = if sim then ".hex" else ".mif"

-- Constructor
makeDataMemInit :: Bool -> Module DataMem
makeDataMemInit sim =
    sequence [makeRAMInit ("data_" ++ show i ++ ext) | i <- [0..7]]
  where ext = if sim then ".hex" else ".mif"


-- Byte, half-word, or word access?
isByteAccess, isHalfAccess, isWordAccess, isDoubleAccess :: AccessWidth -> Bit 1
isByteAccess = (.==. 0b00)
isHalfAccess = (.==. 0b01)
isWordAccess = (.==. 0b10)
isDoubleAccess = (.==. 0b11)

accessWidthToSize :: AccessWidth -> Bit 4
accessWidthToSize width =
  if width .==. 0 then 1
  else if width .==. 1 then 2
  else if width .==. 2 then 4
  else if width .==. 3 then 8
  else 0

-- ======================
-- Writing to data memory
-- ======================

-- Determine byte enables given access width and address
-- TODO clean this up
genByteEnable :: AccessWidth -> Bit 32 -> [Bit 1]
genByteEnable w addr =
  selectList [
    isDoubleAccess w --> [1 | i <- [0..7]]
  , isWordAccess w   --> [a.==.0, a.==.0, a.==.0, a.==.0, a.==.4, a.==.4, a.==.4, a.==.4]
  , isHalfAccess w   --> [a.==.0, a.==.0, a.==.2, a.==.2, a.==.4, a.==.4, a.==.6, a.==.6]
  , isByteAccess w   --> [a.==.0, a.==.1, a.==.2, a.==.3, a.==.4, a.==.5, a.==.6, a.==.7]
  ]
  where a :: Bit 3 = truncate addr

-- Align a write using access width
writeAlign :: AccessWidth -> Bit 64 -> [Bit 8]
writeAlign w d =
  selectList [
    isDoubleAccess w --> [b0, b1, b2, b3, b4, b5, b6, b7]
  , isWordAccess w   --> [b0, b1, b2, b3, b0, b1, b2, b3]
  , isHalfAccess w   --> [b0, b1, b0, b1, b0, b1, b0, b1]
  , isByteAccess w   --> [b0, b0, b0, b0, b0, b0, b0, b0]
  ]
  where
    b0 = slice @7 @0 d
    b1 = slice @15 @8 d
    b2 = slice @23 @16 d
    b3 = slice @31 @24 d
    b4 = slice @39 @32 d
    b5 = slice @47 @40 d
    b6 = slice @55 @48 d
    b7 = slice @63 @56 d

-- Write to data memory
dataMemWrite :: DataMem -> AccessWidth -> Bit 32 -> Bit 64 -> Action ()
dataMemWrite dataMem w addr d =
  sequence_
    [ when byteEn do
        let writeAddr = lower (upper addr :: Bit 29)
        store mem writeAddr byte
        --display "stored " byte " at " addr
    | (mem, byte, byteEn) <- zip3 dataMem bytes byteEns
    ]
  where
    bytes = writeAlign w d
    byteEns = genByteEnable w addr

-- ========================
-- Reading from data memory
-- ========================

-- Process output of data memory using low address bits,
-- access width, and unsigned flag.
readMux :: DataMem -> Bit 32 -> AccessWidth -> Bit 1 -> Bit 64
readMux dataMem addr width isUnsigned =
    select [
      isDoubleAccess width --> b7 # b6 # b5 # b4 # b3 # b2 # b1 # b0
    , isWordAccess width   --> wExt # w
    , isHalfAccess width   --> hExt # h
    , isByteAccess width   --> bExt # b
    ]
  where
    a = lower addr :: Bit 3
    b = select [
          a .==. 0 --> b0
        , a .==. 1 --> b1
        , a .==. 2 --> b2
        , a .==. 3 --> b3
        , a .==. 4 --> b4
        , a .==. 5 --> b5
        , a .==. 6 --> b6
        , a .==. 7 --> b7
        ]
    h = select [
          slice @2 @1 a .==. 0 --> b1 # b0
        , slice @2 @1 a .==. 1 --> b3 # b2
        , slice @2 @1 a .==. 2 --> b5 # b4
        , slice @2 @1 a .==. 3 --> b7 # b6
        ]
    w = (at @2 a .==. 0) ? (b3 # b2 # b1 # b0, b7 # b6 # b5 # b4)
    bExt = isUnsigned ? (0, signExtend (at @7 b))
    hExt = isUnsigned ? (0, signExtend (at @15 h))
    wExt = isUnsigned ? (0, signExtend (at @31 w))
    [b0, b1, b2, b3, b4, b5, b6, b7] = map out dataMem

-- Read from data memory
dataMemRead :: DataMem -> Bit 32 -> Action ()
dataMemRead dataMem addr =
    sequence_ [load mem a | mem <- dataMem]
  where a = lower (upper addr :: Bit 29)

-- TODO ask what happens if i try to access a memory location using an immediate
-- value that causes the address to become inexact (is this a thing that can even
-- happen? what about if it's ddc-relative where you add on the rs1 to the address
-- of ddc? can this make it inexact?)
cheriLoadChecks :: Bit 93 -> Bit 32 -> AccessWidth -> Bit 5
cheriLoadChecks cap addr width =

  if (cap.isValidCap.inv) then
    0x02
  else if (cap.isSealed) then
    0x03
  else if (isDoubleAccess width .&. inv (at @4 (cap.getPerms))) then
    0x14
  else if ((at @2 (cap.getPerms)).inv) then
    0x12
  else if (addr .<. cap.getBase) then
    0x01
  else if (zeroExtend (addr + zeroExtend (accessWidthToSize width)) .>. cap.getTop) then
    0x01
  else
    0

cheriStoreChecks :: Bit 93 -> Bit 32 -> AccessWidth -> Bit 5
cheriStoreChecks cap addr width =
  if (cap.isValidCap.inv) then
    0x02
  else if (cap.isSealed) then
    0x03
  else if (isDoubleAccess width .&. inv (at @5 (cap.getPerms))) then
    0x15
  else if ((at @3 (cap.getPerms)).inv) then
    0x13
  else if (addr .<. cap.getBase) then
    0x01
  else if (zeroExtend (addr + zeroExtend (accessWidthToSize width)) .>. cap.getTop) then
    0x01
  else
    0
