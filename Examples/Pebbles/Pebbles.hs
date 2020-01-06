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

-- RVFI imports
import RVFI_DII

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
  let amount = reg ? (range @4 @0 (s.opB), imm)
  s.result <== s.opA .<<. amount

right :: State -> Bit 1 -> Bit 5 -> Bit 1 -> Action ()
right s arith imm reg = do
  let ext = arith ? (index @31 (s.opA), 0)
  let amount = reg ? (range @4 @0 (s.opB), imm)
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

memRead_0 :: State -> Action ()
memRead_0 s = s.late <== 1

memRead_1_old :: State -> DataMem -> CSRUnit -> Bit 12 -> Action ()
memRead_1_old s mem csrUnit imm =
--  if (((s.opA + signExtend imm) .>=. 0x80000000) .&. ((s.opA + signExtend imm) .<. 0x80010000)
--     .&. (range @1 @0 (s.opA + signExtend imm) .==. 0)) then
    dataMemRead mem (s.opA + signExtend imm)
    --display (range @1 @0 (s.opA + signExtend imm))
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
  s.result <== readMux mem (s.opA + signExtend imm) width unsigned

memRead_1 :: State -> MemIn -> CSRUnit -> Bit 12 -> Bit 2 -> Action ()
memRead_1 s memIn csrUnit imm width = do
  memIn.addr <== s.opA + signExtend imm
  memIn.request <== 1
  memIn.write_memIn <== 0
  memIn.width_memIn <== width
  memIn.value_memIn <== 0

memRead_2 :: State -> MemOut -> CSRUnit -> Bit 12 -> Bit 1 -> Bit 2 -> Action ()
memRead_2 s memOut csrUnit imm unsigned width =
  if (isSome (memOut.value_memOut)) then
    s.result <== memOut.value_memOut.val
  else
    trap s csrUnit (Exception exc_loadAccessFault)

memWrite_old :: State -> DataMem -> CSRUnit -> Bit 12 -> Bit 2 -> Action ()
memWrite_old s mem csrUnit imm width = do
  if ((s.opA + signExtend imm .>=. 0x80000000) .&. (s.opA + signExtend imm .<. 0x80010000)
    .&. (range @1 @0 (s.opA + signExtend imm) .==. 0)) then
    dataMemWrite mem width (s.opA + signExtend imm) (s.opB)
  else
    trap s csrUnit (Exception exc_storeAMOAccessFault)

memWrite_1 :: State -> MemIn -> CSRUnit -> Bit 12 -> Bit 2 -> Action ()
memWrite_1 s memIn csrUnit imm width = do
  memIn.addr <== s.opA + signExtend imm
  memIn.request <== 1
  memIn.write_memIn <== 1
  memIn.width_memIn <== width
  memIn.value_memIn <== s.opB

memWrite_2 :: State -> MemOut -> CSRUnit -> Action ()
memWrite_2 s memOut csrUnit = do
  when (isNone (memOut.value_memOut)) do
    display "memwrite 2 error"
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

-- RV32I CPU, with UART input and output channels
-- TODO discuss:
{-
    make this bool -> bool -> DII_AND_UART -> Module DII_AND_UART
    where DII_AND_UART is a record containing Maybe DII, UART
    does this make sense for synthesis?
    having sim = false and RVFI connections might make sense?
    assume so for now
-}
-- makePebbles :: Bool -> Stream (Bit 8) -> Module (Stream (Bit 8))
makePebbles :: Bool -> RVFI_DII_In -> Module (RVFI_DII_Out)
--makePebbles :: Bool -> Stream (Bit 8) -> Stream (Bit 32)-> Module (Stream (Bit 8))
-- makePebbles sim uartIn = do
makePebbles sim dii_in = do
  -- Tightly-coupled data memory
  -- TODO can i replace this with a . operator?
  --let uartIn = uartInput dii_in
  let insnIn = insnInput dii_in
  let uartIn = uartInput dii_in

  memAddr <- makeWire 0
  memRequest <- makeWire 0
  memWrite_memIn <- makeWire 0
  memWidth_memIn <- makeWire 0
  memValue_memIn <- makeWire 0

  let memInput = MemIn {
    addr = memAddr,
    request = memRequest,
    write_memIn = memWrite_memIn,
    width_memIn = memWidth_memIn,
    value_memIn = memValue_memIn
  }

  mem <- makeDataMem sim
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
  rvfi_dii_data <-  makeCPUPipeline sim (Config { srcA = range @19 @15,
                                                  srcB = range @24 @20,
                                                  dst  = range @11 @7,
                                                  preExecRules = preExecute,
                                                  execRules = execute,
                                                  postExecRules = postExecute
                                                }) insnIn


  return $ RVFI_DII_Out {uart_output = uartOut, rvfi_dii_data = rvfi_dii_data}
