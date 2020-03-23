import Pebbles
import Blarney
import Blarney.Stream

-- Simulation version
{-
simPebbles :: Module ()
simPebbles = do
  uartOut <- makePebbles True nullStream nullStream
  always do
    when (uartOut.canPeek) do
      display_ "%c" (uartOut.peek)
      uartOut.consume
      -}

main :: IO ()
main = do
  --writeVerilogTop simPebbles "SimPebbles" "Pebbles-Verilog/"
  --makePebbles True
  writeVerilogModule (makePebbles True True) "Pebbles" "Pebbles-Verilog/"
  writeVerilogModule (makePebbles True True) "SimPebbles" "Pebbles-Verilog/"
