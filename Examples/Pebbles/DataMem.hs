-- 32-bit wide tightly-coupled data memory
module DataMem where

import Blarney
import Blarney.RAM
import Blarney.Option

-- Data memory size in bytes
type LogDataMemSize = 16

-- Implement data memory as four block RAMs
-- (one for each byte of word)
type DataMem = [RAM (Bit (LogDataMemSize-2)) (Bit 8)]

-- RV32I memory access width
type AccessWidth = Bit 2

-- TODO do these really need to be Wires?
data MemIn = MemIn {
  addr :: Wire (Bit 32),
  request :: Wire (Bit 1),
  write_memIn :: Wire (Bit 1),
  width_memIn :: Wire (AccessWidth),
  value_memIn :: Wire (Bit 32)
} deriving (Generic, Interface)

data MemOut = MemOut {
  value_memOut :: Option (Bit 32)
} deriving (Generic, Bits)

memBase = 0x80000000
memSize = 0x10000

makeDataMemCore :: Bool -> MemIn -> Module (MemOut)
makeDataMemCore sim req = do
  dataMem :: DataMem <- makeDataMem sim

  readPending :: Reg (Bit 1) <- makeReg 0
  readPendingWidth :: Reg (AccessWidth) <- makeReg dontCare
  errPending :: Reg (Bit 1) <- makeDReg 0

  -- TODO this probably shouldn't be a wire
  responseData :: Wire (Bit 32) <- makeWire 0

  always do
    let isUnaligned = select [ isWordAccess (req.width_memIn.val) --> range @1 @0 (req.addr.val) .!=. 0
                             , isHalfAccess (req.width_memIn.val) --> bit 0 (req.addr.val) .!=. 0
                             , isByteAccess (req.width_memIn.val) --> 0
                             ]
    -- read logic part 1
    readPending <== req.request.active .&. req.request.val .&. req.write_memIn.val.inv
    readPendingWidth <== req.width_memIn.val

    when ((req.request.val) .&. (req.write_memIn.val.inv) .&. (req.request.active)) do
      when ((req.addr.val .>=. memBase) .&. (req.addr.val .<. memBase + memSize) .&. (isUnaligned.inv)) do
        dataMemRead dataMem (req.addr.val)

      when ((req.addr.val .<. memBase) .|. (req.addr.val .>=. memBase + memSize) .|. (isUnaligned)) do
        display "out of bounds"
        errPending <== 1

    -- read logic part 2
    when (readPending.val) do
      let [b0, b1, b2, b3] = map out dataMem
      let wAligned = b3 # b2 # b1 # b0
      let hAligned = 0 # ((index @1 (req.addr.val) .==. 0) ? (b1 # b0, b3 # b2))
      -- TODO clean this up into a case statement?
      let bAligned = select [ range @1 @0 (req.addr.val) .==. 0 --> 0 # b0
                            , range @1 @0 (req.addr.val) .==. 1 --> 0 # b1
                            , range @1 @0 (req.addr.val) .==. 2 --> 0 # b2
                            , range @1 @0 (req.addr.val) .==. 3 --> 0 # b3
                            ]
      responseData <== select [
          isWordAccess (readPendingWidth.val) --> wAligned
        , isHalfAccess (readPendingWidth.val) --> hAligned
        , isByteAccess (readPendingWidth.val) --> bAligned
        ]



    -- write logic
    when ((req.request.val) .&. (req.write_memIn.val) .&. (req.request.active)) do
      when ((req.addr.val .>=. memBase) .&. (req.addr.val .<. memBase + memSize) .&. (isUnaligned.inv)) do
        dataMemWrite dataMem (req.width_memIn.val) (req.addr.val) (req.value_memIn.val)
        display "test statement"
      when ((req.addr.val .<. memBase) .|. (req.addr.val .>=. memBase + memSize) .|. (isUnaligned)) do
        errPending <== 1
        display "************** address 0x" (req.addr.val) " causes error"


  return MemOut {
    value_memOut = errPending.val ? (none, some (responseData.val))
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
    b0 = range @7 @0 d
    b1 = range @15 @8 d
    b2 = range @23 @16 d
    b3 = range @31 @24 d

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
    h = (index @1 a .==. 0) ? (b1 # b0, b3 # b2)
    bExt = isUnsigned ? (0, signExtend (index @7 b))
    hExt = isUnsigned ? (0, signExtend (index @15 h))
    [b0, b1, b2, b3] = map out dataMem

-- Read from data memory
dataMemRead :: DataMem -> Bit 32 -> Action ()
dataMemRead dataMem addr =
    sequence_ [load mem a | mem <- dataMem]
  where a = lower (upper addr :: Bit 30)



-- functions intended for external use
--dataMemWriteReq
--dataMemReadReq
--dataMemGetReadResp
--dataMemGetWriteResp
