#include "VSimPebbles.h"
#include <verilated.h>

#include <fstream>
#include <iostream>
#include <iomanip>
#include <cstdint>
#include <vector>
#include <unistd.h>
#include "socket_packet_utils.c"
#include <stdlib.h>
#if VM_TRACE
#include <verilated_vcd_c.h>
#endif

#define MEM_BASE_BYTES 0x80000000
#define MEM_BASE_WORDS 0x20000000
#define MEM_SIZE_BYTES 0x10000
#define MEM_SIZE_WORDS 0x2000000/4

struct RVFI_DII_Execution_Packet {
    std::uint64_t rvfi_order : 64;      // [00 - 07] Instruction number:      INSTRET value after completion.
    std::uint64_t rvfi_pc_rdata : 64;   // [08 - 15] PC before instr:         PC for current instruction
    std::uint64_t rvfi_pc_wdata : 64;   // [16 - 23] PC after instr:          Following PC - either PC + 4 or jump/trap target.
    std::uint64_t rvfi_insn : 64;       // [24 - 31] Instruction word:        32-bit command value.
    std::uint64_t rvfi_rs1_data : 64;   // [32 - 39] Read register values:    Values as read from registers named
    std::uint64_t rvfi_rs2_data : 64;   // [40 - 47]                          above. Must be 0 if register ID is 0.
    std::uint64_t rvfi_rd_wdata : 64;   // [48 - 55] Write register value:    MUST be 0 if rd_ is 0.
    std::uint64_t rvfi_mem_addr : 64;   // [56 - 63] Memory access addr:      Points to byte address (aligned if define
                                        //                                      is set). *Should* be straightforward.
                                        //                                      0 if unused.
    std::uint64_t rvfi_mem_rdata : 64;  // [64 - 71] Read data:               Data read from mem_addr (i.e. before write)
    std::uint64_t rvfi_mem_wdata : 64;  // [72 - 79] Write data:              Data written to memory by this command.
    std::uint8_t rvfi_mem_rmask : 8;    // [80]      Read mask:               Indicates valid bytes read. 0 if unused.
    std::uint8_t rvfi_mem_wmask : 8;    // [81]      Write mask:              Indicates valid bytes written. 0 if unused.
    std::uint8_t rvfi_rs1_addr : 8;     // [82]      Read register addresses: Can be arbitrary when not used,
    std::uint8_t rvfi_rs2_addr : 8;     // [83]                          otherwise set as decoded.
    std::uint8_t rvfi_rd_addr : 8;      // [84]      Write register address:  MUST be 0 if not used.
    std::uint8_t rvfi_trap : 8;         // [85] Trap indicator:          Invalid decode, misaligned access or
                                        //                                      jump command to misaligned address.
    std::uint8_t rvfi_halt : 8;         // [86] Halt indicator:          Marks the last instruction retired 
                                        //                                      before halting execution.
    std::uint8_t rvfi_intr : 8;         // [87] Trap handler:            Set for first instruction in trap handler.     
};

struct RVFI_DII_Instruction_Packet {
    std::uint32_t dii_insn : 32;      // [0 - 3] Instruction word: 32-bit instruction or command. The lower 16-bits
                                      // may decode to a 16-bit compressed instruction.
    std::uint16_t dii_time : 16;      // [5 - 4] Time to inject token.  The difference between this and the previous
                                      // instruction time gives a delay before injecting this instruction.
                                      // This can be ignored for models but gives repeatability for implementations
                                      // while shortening counterexamples.
    std::uint8_t dii_cmd : 8;         // [6] This token is a trace command.  For example, reset device under test.
    std::uint8_t padding : 8;         // [7]
};

RVFI_DII_Execution_Packet readRVFI(VSimPebbles *top, bool signExtend);
void sendReturnTrace(std::vector<RVFI_DII_Execution_Packet> &returnTrace, unsigned long long socket);


vluint64_t main_time = 0;
// Called by $time in Verilog
double sc_time_stamp () {
  return main_time;
}

int main(int argc, char** argv, char** env) {

    Verilated::commandArgs(argc, argv);
    VSimPebbles* top = new VSimPebbles;

    // set up tracing
    #if VM_TRACE
    std::cout << "tracing" << std::endl;
    Verilated::traceEverOn(true);
    VerilatedVcdC trace_obj;
    top->trace(&trace_obj, 99);
    trace_obj.open("vlt_d.vcd");
    #endif

    // set up initial core inputs
    top->clock = 0;
    top->reset = 1;
    top->eval();

    top->reset = 0;
    top->eval();

    while (1) {
        top->clock = 1;
        top->eval();
        top->clock = 0;
        top->eval();
    }

    std::cout << "finished" << std::endl << std::flush;
    delete top;
    exit(0);
}


// send the return trace that is passed in over the socket that is passed in
void sendReturnTrace(std::vector<RVFI_DII_Execution_Packet> &returntrace, unsigned long long socket) {
    const int BULK_SEND = 50;

    std::cout << "sending trace" << std::endl;

    if (returntrace.size() > 0) {
        int tosend = 1;
        for (int i = 0; i < returntrace.size(); i+=tosend) {
            tosend = 1;
            RVFI_DII_Execution_Packet sendarr[BULK_SEND];
            sendarr[0] = returntrace[i];

            // bulk send if possible
            if (returntrace.size() - i > BULK_SEND) {
                tosend = BULK_SEND;
                for (int j = 0; j < tosend; j++) {
                    sendarr[j] = returntrace[i+j];
                }
            }

            // loop to make sure that the packet has been properly sent
            while (
                !serv_socket_putN(socket, sizeof(RVFI_DII_Execution_Packet) * tosend, (unsigned int *) sendarr)
            ) {
                //std::cout << "sending" << std::endl;
                // empty
            }
        }
        //std::cout << "clearing" << std::endl;
        returntrace.clear();
    }
}

RVFI_DII_Execution_Packet readRVFI(VSimPebbles *top, bool signExtend) {
    unsigned long long signExtension;
    if (signExtend) {
        signExtension = 0xFFFFFFFF00000000;
    } else {
        signExtension = 0x0000000000000000;
    }

    /*
    RVFI_DII_Execution_Packet execpacket = {
        .rvfi_order = top->rvfi_order,
        .rvfi_pc_rdata = top->rvfi_pc_rdata     | ((top->rvfi_pc_rdata & 0x80000000) ? signExtension : 0),
        .rvfi_pc_wdata = top->rvfi_pc_wdata     | ((top->rvfi_pc_wdata & 0x80000000) ? signExtension : 0),
        .rvfi_insn = top->rvfi_insn             | ((top->rvfi_insn & 0x80000000) ? signExtension : 0 ),
        .rvfi_rs1_data = top->rvfi_rs1_rdata    | ((top->rvfi_rs1_rdata & 0x80000000) ? signExtension : 0 ),
        .rvfi_rs2_data = top->rvfi_rs2_rdata    | ((top->rvfi_rs2_rdata & 0x80000000) ? signExtension : 0 ),
        .rvfi_rd_wdata = top->rvfi_rd_wdata     | ((top->rvfi_rd_wdata & 0x80000000) ? signExtension : 0 ),
        .rvfi_mem_addr = top->rvfi_mem_addr     | ((top->rvfi_mem_addr & 0x80000000) ? signExtension : 0 ),
        .rvfi_mem_rdata = top->rvfi_mem_rdata   | ((top->rvfi_mem_rdata & 0x80000000) ? signExtension : 0 ),
        .rvfi_mem_wdata = top->rvfi_mem_wdata   | ((top->rvfi_mem_wdata & 0x80000000) ? signExtension : 0 ),
        .rvfi_mem_rmask = top->rvfi_mem_rmask,
        .rvfi_mem_wmask = top->rvfi_mem_wmask,
        .rvfi_rs1_addr = top->rvfi_rs1_addr,
        .rvfi_rs2_addr = top->rvfi_rs2_addr,
        .rvfi_rd_addr = top->rvfi_rd_addr,
        .rvfi_trap = top->rvfi_trap,
        .rvfi_halt = top->rst_i,
        .rvfi_intr = top->rvfi_intr
    };*/

    RVFI_DII_Execution_Packet execpacket = {
        .rvfi_order = 0,
        .rvfi_pc_rdata = top->out_rvfi_dii_data_rvfi_data_rvfi_pc_rdata,
        .rvfi_pc_wdata = top->out_rvfi_dii_data_rvfi_data_rvfi_pc_wdata,
        .rvfi_insn = top->out_rvfi_dii_data_rvfi_data_rvfi_insn,
        .rvfi_rs1_data = top->out_rvfi_dii_data_rvfi_data_rvfi_rs1_data,
        .rvfi_rs2_data = top->out_rvfi_dii_data_rvfi_data_rvfi_rs2_data,
        .rvfi_rd_wdata = top->out_rvfi_dii_data_rvfi_data_rvfi_rd_wdata,
        .rvfi_mem_addr = top->out_rvfi_dii_data_rvfi_data_rvfi_mem_addr,
        .rvfi_mem_rdata = top->out_rvfi_dii_data_rvfi_data_rvfi_mem_rdata,
        .rvfi_mem_wdata = top->out_rvfi_dii_data_rvfi_data_rvfi_mem_wdata,
        .rvfi_mem_rmask = top->out_rvfi_dii_data_rvfi_data_rvfi_mem_rmask,
        .rvfi_mem_wmask = top->out_rvfi_dii_data_rvfi_data_rvfi_mem_wmask,
        .rvfi_rs1_addr = top->out_rvfi_dii_data_rvfi_data_rvfi_rs1_addr,
        .rvfi_rs2_addr = top->out_rvfi_dii_data_rvfi_data_rvfi_rs2_addr,
        .rvfi_rd_addr = top->out_rvfi_dii_data_rvfi_data_rvfi_rd_addr,
        .rvfi_trap = top->out_rvfi_dii_data_rvfi_data_rvfi_trap,
        .rvfi_halt = top->reset,
        .rvfi_intr = 0
    };

    return execpacket;
}


