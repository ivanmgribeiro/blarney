module RVFI_DII where

import Blarney
import Blarney.Stream

data RVFI_DII_Data = RVFI_DII_Data { rvfi_pc_rdata :: Bit 32
                                   , rvfi_pc_wdata :: Bit 32
                                   , rvfi_insn     :: Bit 32
                                   , rvfi_rs1_data :: Bit 32
                                   , rvfi_rs2_data :: Bit 32
                                   , rvfi_rd_wdata :: Bit 32
                                   , rvfi_mem_addr :: Bit 32
                                   , rvfi_mem_rdata :: Bit 32
                                   , rvfi_mem_wdata :: Bit 32
                                   , rvfi_mem_rmask :: Bit 4
                                   , rvfi_mem_wmask :: Bit 4
                                   , rvfi_rs1_addr :: Bit 5
                                   , rvfi_rs2_addr :: Bit 5
                                   , rvfi_rd_addr :: Bit 5
                                   , rvfi_trap :: Bit 1
                                   }

data RVFI_DII_In = RVFI_DII_In { uartInput :: Stream (Bit 8)
                               -- TODO replace with Maybe Stream
                               , insnInput :: Stream (Bit 32)
                               }


data RVFI_DII_Out = RVFI_DII_Out { uartOutput :: Stream (Bit 8)
                                 , rvfiData :: Maybe RVFI_DII_Data
                                 }
                                 

