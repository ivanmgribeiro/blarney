module CHERITrap where

import Blarney

import CSR
import Trap
import Pipeline
import CHERIBlarneyWrappers

type CHERIExceptionCode = Bit 5
cheri_exc_lengthViolation               :: CHERIExceptionCode = 0x01
cheri_exc_tagViolation                  :: CHERIExceptionCode = 0x02
cheri_exc_sealViolation                 :: CHERIExceptionCode = 0x03
cheri_exc_typeViolation                 :: CHERIExceptionCode = 0x04
cheri_exc_callTrap                      :: CHERIExceptionCode = 0x05
cheri_exc_returnTrap                    :: CHERIExceptionCode = 0x06
cheri_exc_sysStackUnderflow             :: CHERIExceptionCode = 0x07
cheri_exc_softDefPermViolation          :: CHERIExceptionCode = 0x08
cheri_exc_mmuProhibitsStoreViolation    :: CHERIExceptionCode = 0x09
cheri_exc_representabilityViolation     :: CHERIExceptionCode = 0x0a
cheri_exc_unalignedBaseViolation        :: CHERIExceptionCode = 0x0b
cheri_exc_globalViolation               :: CHERIExceptionCode = 0x10
cheri_exc_permitExecuteViolation        :: CHERIExceptionCode = 0x11
cheri_exc_permitLoadViolation           :: CHERIExceptionCode = 0x12
cheri_exc_permitStoreViolation          :: CHERIExceptionCode = 0x13
cheri_exc_permitLoadCapViolation        :: CHERIExceptionCode = 0x14
cheri_exc_permitStoreCapViolation       :: CHERIExceptionCode = 0x15
cheri_exc_permitStoreLocalCapViolation  :: CHERIExceptionCode = 0x16
cheri_exc_permitSealViolation           :: CHERIExceptionCode = 0x17
cheri_exc_accessSysRegsViolation        :: CHERIExceptionCode = 0x18
cheri_exc_permitCCallViolation          :: CHERIExceptionCode = 0x19
cheri_exc_permitCCallIDCViolation       :: CHERIExceptionCode = 0x1a
cheri_exc_unsealViolation               :: CHERIExceptionCode = 0x1b
cheri_exc_setCIDViolation               :: CHERIExceptionCode = 0x1c

-- TODO rewrite this in a cleaner way
--prettyPrint :: CHERIExceptionCode -> String
--prettyPrint c =
--  if c .==. cheri_exc_lengthViolation then
--    "length violation"
--  else if c .==. cheri_exc_tagViolation then
--    "tag violation"
--  else if c .==. cheri_exc_sealViolation then
--    "seal violation"
--  else if c .==. cheri_exc_typeViolation then
--    "type violation"
--  else if c .==. cheri_exc_callTrap then
--    "call trap"
--  else if c .==. cheri_exc_returnTrap then
--    "return trap"
--  else if c .==. cheri_exc_sysStackUnderflow then
--    "system trusted stack underflow"
--  else if c .==. cheri_exc_softDefPermViolation then
--    "software/user defined violation"
--  else if c .==. cheri_exc_mmuProhibitsStoreViolation then
--    "mmu prohibits store violation"
--  else if c .==. cheri_exc_representabilityViolation then
--    "representability/exact violation"
--  else if c .==. cheri_exc_unalignedBaseViolation then
--    "unaligned base violation"
--  else if c .==. cheri_exc_globalViolation then
--    "global violation"
--  else if c .==. cheri_exc_permitExecuteViolation then
--    "permit execute violation"
--  else if c .==. cheri_exc_permitLoadViolation then
--    "permit load violation"
--  else if c .==. cheri_exc_permitStoreViolation then
--    "permit store violation"
--  else if c .==. cheri_exc_permitLoadCapViolation then
--    "permit load cap violation"
--  else if c .==. cheri_exc_permitStoreCapViolation then
--    "permit store cap violation"
--  else if c .==. cheri_exc_permitStoreLocalCapViolation then
--    "permit store local cap violation"
--  else if c .==. cheri_exc_permitSealViolation then
--    "permit seal violation"
--  else if c .==. cheri_exc_accessSysRegsViolation then
--    "access system registers violation"
--  else if c .==. cheri_exc_permitCCallViolation then
--    "permit ccall violation"
--  else if c .==. cheri_exc_permitCCallIDCViolation then
--    "permit ccall idc violation"
--  else if c .==. cheri_exc_unsealViolation then
--    "unseal violation"
--  else if c .==. cheri_exc_setCIDViolation then
--    "set CID violation"
--  else
--    "unknown cheri exception code"

cheriTrap :: Bool -> State -> CSRUnit -> CHERIExceptionCode -> Bit 6 -> Action ()
cheriTrap delay s csrUnit c reg =
  if delay then do
    -- TODO write register number as well
    display "CHERI TRAP CALLED @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
    display "exception code: " c
    --(csrUnit.writeCSR) 0xBC0 (zeroExtend c)
    s.mccsr <== (zeroExtend (reg # c # (0 :: Bit 5)))
    s.mepcc <== s.pcc.val
    csrUnit.mepc <== s.pc.val
    csrUnit.mcause <== toCause (Exception exc_CHERIException)
    --s.pc  <== csrUnit.mtvec.val
    s.pcc_delay <== lower ((s.mtcc.val.setOffset) (s.mtcc.val.getOffset .&. 0xfffffffc))
    --display "setting mepc to value " (s.pc.val)
    --display "setting mepcc to value " (s.pcc.val)
    --s.exc <== 1
    s.exc_delay <== 1
  else do
    -- TODO write register number as well
    display "CHERI TRAP CALLED @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
    display "exception code: " c
    --(csrUnit.writeCSR) 0xBC0 (zeroExtend c)
    s.mccsr <== (zeroExtend (reg # c # (0 :: Bit 5)))
    s.mepcc <== s.pcc.val
    csrUnit.mepc <== s.pc.val
    csrUnit.mcause <== toCause (Exception exc_CHERIException)
    --s.pc  <== csrUnit.mtvec.val
    s.pcc <== lower ((s.mtcc.val.setOffset) (s.mtcc.val.getOffset .&. 0xfffffffc))
    --display "setting mepc to value " (s.pc.val)
    --display "setting mepcc to value " (s.pcc.val)
    s.exc <== 1

