-- 32-bit wide tightly-coupled data memory
module DataMem where

import Blarney
import Blarney.RAM
import Blarney.Option

-- Data memory size in bytes
type LogDataMemSize = 16

-- memory base & size constants
-- TODO make LogDataMemSize depend on these
memBase = 0x80000000
memSize = 0x10000

-- Implement data memory as four block RAMs
-- (one for each byte of word)
type DataMem = [RAM (Bit (LogDataMemSize-2)) (Bit 8)]

-- RV32I memory access width
type AccessWidth = Bit 2

-- TODO do these really need to be Wires?
data MemReq = MemReq {
  memReqAddr :: Bit 32,
  memReqWrite :: Bit 1,
  memReqWidth :: AccessWidth,
  memReqValue :: Bit 32
} deriving (Generic, Bits)

data MemResp = MemResp {
  memRespValue :: Option (Bit 32)
} deriving (Generic, Bits)

type MemIn = Wire MemReq

-- TODO extend this to take in the memory base & size
makeDataMemCore :: Bool -> MemIn -> Module MemResp
makeDataMemCore sim memIn = do
  dataMem :: DataMem <- makeDataMem sim

  -- information about the pending request
  -- TODO might make more sense to just make a Reg (MemReq) to hold this,
  -- or to use old
  readPending :: Reg (Bit 1) <- makeReg 0
  readPendingWidth :: Reg (AccessWidth) <- makeReg dontCare
  readPendingAlignment :: Reg (Bit 2) <- makeReg dontCare
  errPending :: Reg (Bit 1) <- makeDReg 0

  -- TODO this probably shouldn't be a wire
  responseData :: Wire (Bit 32) <- makeWire 0

  always do
    let addrBottom = slice @1 @0 (memIn.val.memReqAddr)
    -- check if the address is unaligned with respect to the memory access width
    let isUnaligned = if isWordAccess (memIn.val.memReqWidth) then
                        addrBottom .!=. 0
                      else if isHalfAccess (memIn.val.memReqWidth) then
                        at @0 (memIn.val.memReqAddr) .!=. 0
                      else
                        0

    ------------------------------

    ----      READ LOGIC      ----

    ------------------------------

    -- read logic part 1
    -- test if memory address is valid and if it is, set the proper
    -- inputs to load the data
    -- if not, don't request anything and trigger an error
    readPending <== memIn.active .&. memIn.val.memReqWrite.inv
    readPendingWidth <== memIn.val.memReqWidth
    readPendingAlignment <== addrBottom

    when (memIn.active .&. memIn.val.memReqWrite.inv) do
      if ((memIn.val.memReqAddr .>=. memBase)
         .&. (memIn.val.memReqAddr .<. memBase + memSize)
         .&. (isUnaligned.inv)) then
        dataMemRead dataMem (memIn.val.memReqAddr)
      else
        errPending <== 1

    -- read logic part 2
    -- get the memory values that were read and set the response signals
    when (readPending.val) do
      responseData <== readMux dataMem
                               (0 # readPendingAlignment.val)
                               (readPendingWidth.val)
                               1

    -------------------------------

    ----      WRITE LOGIC      ----

    -------------------------------

    -- write logic
    -- test if memory address is valid and if it is, set the proper
    -- inputs to store the data
    -- if not, don't request anything and trigger an error
    when (memIn.active .&. memIn.val.memReqWrite) do
      if ((memIn.val.memReqAddr .>=. memBase)
         .&. (memIn.val.memReqAddr .<. memBase + memSize)
         .&. (isUnaligned.inv)) then
        dataMemWrite dataMem
                     (memIn.val.memReqWidth)
                     (memIn.val.memReqAddr)
                     (memIn.val.memReqValue)
      else
        errPending <== 1


  return MemResp {
    memRespValue = errPending.val ? (none, some (responseData.val))
  }


-- Constructor
makeDataMem :: Bool -> Module DataMem
makeDataMem sim =
    sequence [makeRAM | i <- [0..3]]
  where ext = if sim then ".hex" else ".mif"

-- Constructor
makeDataMemInit :: Bool -> Module DataMem
makeDataMemInit sim =
    sequence [makeRAMInit ("data_" ++ show i ++ ext) | i <- [0..3]]
  where ext = if sim then ".hex" else ".mif"


-- Byte, half-word, or word access?
isByteAccess, isHalfAccess, isWordAccess :: AccessWidth -> Bit 1
isByteAccess = (.==. 0b00)
isHalfAccess = (.==. 0b01)
isWordAccess = (.==. 0b10)

-- ======================
-- Writing to data memory
-- ======================

-- Determine byte enables given access width and address
genByteEnable :: AccessWidth -> Bit 32 -> [Bit 1]
genByteEnable w addr =
  selectList [
    isWordAccess w --> [1, 1, 1, 1]
  , isHalfAccess w --> [a.==.0, a.==.0, a.==.2, a.==.2]
  , isByteAccess w --> [a.==.0, a.==.1, a.==.2, a.==.3]
  ]
  where a :: Bit 2 = truncate addr

-- Align a write using access width
writeAlign :: AccessWidth -> Bit 32 -> [Bit 8]
writeAlign w d =
  selectList [
    isWordAccess w --> [b0, b1, b2, b3]
  , isHalfAccess w --> [b0, b1, b0, b1]
  , isByteAccess w --> [b0, b0, b0, b0]
  ]
  where
    b0 = slice @7 @0 d
    b1 = slice @15 @8 d
    b2 = slice @23 @16 d
    b3 = slice @31 @24 d

-- Write to data memory
dataMemWrite :: DataMem -> AccessWidth -> Bit 32 -> Bit 32 -> Action ()
dataMemWrite dataMem w addr d =
  sequence_
    [ when byteEn do
        let writeAddr = lower (upper addr :: Bit 30)
        store mem writeAddr byte
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
readMux :: DataMem -> Bit 32 -> AccessWidth -> Bit 1 -> Bit 32
readMux dataMem addr w isUnsigned =
    select [
      isWordAccess w --> b3 # b2 # b1 # b0
    , isHalfAccess w --> hExt # h
    , isByteAccess w --> bExt # b
    ]
  where
    a = lower addr :: Bit 2
    b = select [
          a .==. 0 --> b0
        , a .==. 1 --> b1
        , a .==. 2 --> b2
        , a .==. 3 --> b3
        ]
    h = (at @1 a .==. 0) ? (b1 # b0, b3 # b2)
    bExt = isUnsigned ? (0, signExtend (at @7 b))
    hExt = isUnsigned ? (0, signExtend (at @15 h))
    [b0, b1, b2, b3] = map out dataMem

-- Read from data memory
dataMemRead :: DataMem -> Bit 32 -> Action ()
dataMemRead dataMem addr =
    sequence_ [load mem a | mem <- dataMem]
  where a = lower (upper addr :: Bit 30)
