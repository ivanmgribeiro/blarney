module InstrMem where

import Blarney
import Blarney.Core.RAM
import Blarney.Option
import CHERIBlarneyWrappers
import Blarney.Stream
-- import this for the type declarations
import DataMem

import RVFI_DII

-- Instruction memory size
type InstrAddr = Bit 14

-- Instructions
type Instr = Bit 32

-- instruction memory request type
data InstrReq = InstrReq {
  instrReqCap :: Bit 93
} deriving (Generic, Bits)

type InstrIn = Wire InstrReq

-- instruction memory response time
data InstrResp = InstrResp {
  instrRespValue :: Bit 32,
  instrRespValid :: Bit 1,
  instrRespErr   :: Bit 1
} deriving (Generic, Bits)

-- TODO do i want this to have this signature or a different one?
-- could implement it by passing the RAM InstrAddr Instr around
-- pros of using MemIn and MemResp: standard with the data memory
-- pros of using RAM: more similar to old DataMem implementation?
-- TODO something else to consider: maybe put this in DataMem since reusing MemReq etc
-- TODO another thing:
--                  if pcfetch fails because of an unauthorized pcc, we still want to get
--                  the instruction so we can pass it to TestRIG
--                  the current DataMem MemRes doesn't support this
-- TODO add option to have DII in here
-- TODO change this from InstrIn to just InstrReq
makeInstrMem :: Bool -> Bool -> InstrIn -> RVFI_DII_In -> Module InstrResp
makeInstrMem sim dii instrIn rvfi_dii_in = do
  if dii then do
    return InstrResp {
      instrRespValue = rvfi_dii_in.insnInput.peek,
      instrRespValid = rvfi_dii_in.insnInput.canPeek,
      instrRespErr = (cheriInstrChecks (instrIn.val.instrReqCap))
    }
  else do
    memIn :: MemIn <- makeWire MemReq { memReqCap = 0
                                      , memReqAddr = 0
                                      , memReqWrite = 0
                                      , memReqWidth = 2
                                      , memReqValue = 0
                                      , memReqTag = 0
                                      }
    memResp <- makeDataMemCore sim memIn

    always do
      let memReq = MemReq {
        memReqCap = instrIn.val.instrReqCap,
        memReqAddr = instrIn.val.instrReqCap.getAddr,
        memReqWrite = 0,
        memReqWidth = 2,
        memReqValue = 0,
        memReqTag = 0
      }

      when (instrIn.active) do
        memIn <== memReq

    -- TODO this is untested
    let instrResp = InstrResp {
      instrRespValue = lower (memResp.memRespValue),
      instrRespValid = 1,
      instrRespErr   = memResp.memRespErr .|. cheriInstrChecks (instrIn.val.instrReqCap)
    }

    return instrResp
    

-- TODO this function is pretty redundant atm - might be clearer to just
-- omit this and perform this in the pipeline?
--loadInstr :: InstrIn -> Bit 93 -> Action ()
--loadInstr instrIn cap = do
--  instrIn <== InstrReq {
--    instrReqCap = cap
--  }

cheriInstrChecks :: Bit 93 -> Bit 1
cheriInstrChecks cap =
  (cap.isValidCap.inv)
  .|. (cap.isSealed)
  .|. (at @1 (cap.getPerms)).inv
  .|. (at @2 (cap.getPerms)).inv
  .|. (cap.getAddr .<. cap.getBase)
  .|. (zeroExtend (cap.getAddr + 4) .>. cap.getTop) -- need to account for instruction size
