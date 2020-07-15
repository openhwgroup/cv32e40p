// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
//                                                                            //
// Design Name:    RISC-V processor core                                      //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Defines for various constants used by the processor core.  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

package cv32e40p_pkg;

////////////////////////////////////////////////
//    ___         ____          _             //
//   / _ \ _ __  / ___|___   __| | ___  ___   //
//  | | | | '_ \| |   / _ \ / _` |/ _ \/ __|  //
//  | |_| | |_) | |__| (_) | (_| |  __/\__ \  //
//   \___/| .__/ \____\___/ \__,_|\___||___/  //
//        |_|                                 //
////////////////////////////////////////////////

parameter OPCODE_SYSTEM    = 7'h73;
parameter OPCODE_FENCE     = 7'h0f;
parameter OPCODE_OP        = 7'h33;
parameter OPCODE_OPIMM     = 7'h13;
parameter OPCODE_STORE     = 7'h23;
parameter OPCODE_LOAD      = 7'h03;
parameter OPCODE_BRANCH    = 7'h63;
parameter OPCODE_JALR      = 7'h67;
parameter OPCODE_JAL       = 7'h6f;
parameter OPCODE_AUIPC     = 7'h17;
parameter OPCODE_LUI       = 7'h37;
parameter OPCODE_OP_FP     = 7'h53;
parameter OPCODE_OP_FMADD  = 7'h43;
parameter OPCODE_OP_FNMADD = 7'h4f;
parameter OPCODE_OP_FMSUB  = 7'h47;
parameter OPCODE_OP_FNMSUB = 7'h4b;
parameter OPCODE_STORE_FP  = 7'h27;
parameter OPCODE_LOAD_FP   = 7'h07;
parameter OPCODE_AMO       = 7'h2F;

// those opcodes are now used for PULP custom instructions
// parameter OPCODE_CUST0     = 7'h0b
// parameter OPCODE_CUST1     = 7'h2b

// PULP custom
parameter OPCODE_LOAD_POST  = 7'h0b;
parameter OPCODE_STORE_POST = 7'h2b;
parameter OPCODE_PULP_OP    = 7'h5b;
parameter OPCODE_VECOP      = 7'h57;
parameter OPCODE_HWLOOP     = 7'h7b;

parameter REGC_S1   = 2'b10;
parameter REGC_S4   = 2'b00;
parameter REGC_RD   = 2'b01;
parameter REGC_ZERO = 2'b11;


//////////////////////////////////////////////////////////////////////////////
//      _    _    _   _    ___                       _   _                  //
//     / \  | |  | | | |  / _ \ _ __   ___ _ __ __ _| |_(_) ___  _ __  ___  //
//    / _ \ | |  | | | | | | | | '_ \ / _ \ '__/ _` | __| |/ _ \| '_ \/ __| //
//   / ___ \| |__| |_| | | |_| | |_) |  __/ | | (_| | |_| | (_) | | | \__ \ //
//  /_/   \_\_____\___/   \___/| .__/ \___|_|  \__,_|\__|_|\___/|_| |_|___/ //
//                             |_|                                          //
//////////////////////////////////////////////////////////////////////////////

parameter ALU_OP_WIDTH = 7;

parameter ALU_ADD   = 7'b0011000;
parameter ALU_SUB   = 7'b0011001;
parameter ALU_ADDU  = 7'b0011010;
parameter ALU_SUBU  = 7'b0011011;
parameter ALU_ADDR  = 7'b0011100;
parameter ALU_SUBR  = 7'b0011101;
parameter ALU_ADDUR = 7'b0011110;
parameter ALU_SUBUR = 7'b0011111;

parameter ALU_XOR   = 7'b0101111;
parameter ALU_OR    = 7'b0101110;
parameter ALU_AND   = 7'b0010101;

// Shifts
parameter ALU_SRA   = 7'b0100100;
parameter ALU_SRL   = 7'b0100101;
parameter ALU_ROR   = 7'b0100110;
parameter ALU_SLL   = 7'b0100111;

// bit manipulation
parameter ALU_BEXT  = 7'b0101000;
parameter ALU_BEXTU = 7'b0101001;
parameter ALU_BINS  = 7'b0101010;
parameter ALU_BCLR  = 7'b0101011;
parameter ALU_BSET  = 7'b0101100;
parameter ALU_BREV  = 7'b1001001;

// Bit counting
parameter ALU_FF1   = 7'b0110110;
parameter ALU_FL1   = 7'b0110111;
parameter ALU_CNT   = 7'b0110100;
parameter ALU_CLB   = 7'b0110101;

// Sign-/zero-extensions
parameter ALU_EXTS  = 7'b0111110;
parameter ALU_EXT   = 7'b0111111;

// Comparisons
parameter ALU_LTS   = 7'b0000000;
parameter ALU_LTU   = 7'b0000001;
parameter ALU_LES   = 7'b0000100;
parameter ALU_LEU   = 7'b0000101;
parameter ALU_GTS   = 7'b0001000;
parameter ALU_GTU   = 7'b0001001;
parameter ALU_GES   = 7'b0001010;
parameter ALU_GEU   = 7'b0001011;
parameter ALU_EQ    = 7'b0001100;
parameter ALU_NE    = 7'b0001101;

// Set Lower Than operations
parameter ALU_SLTS  = 7'b0000010;
parameter ALU_SLTU  = 7'b0000011;
parameter ALU_SLETS = 7'b0000110;
parameter ALU_SLETU = 7'b0000111;

// Absolute value
parameter ALU_ABS   = 7'b0010100;
parameter ALU_CLIP  = 7'b0010110;
parameter ALU_CLIPU = 7'b0010111;

// Insert/extract
parameter ALU_INS   = 7'b0101101;

// min/max
parameter ALU_MIN   = 7'b0010000;
parameter ALU_MINU  = 7'b0010001;
parameter ALU_MAX   = 7'b0010010;
parameter ALU_MAXU  = 7'b0010011;

// div/rem
parameter ALU_DIVU  = 7'b0110000; // bit 0 is used for signed mode, bit 1 is used for remdiv
parameter ALU_DIV   = 7'b0110001; // bit 0 is used for signed mode, bit 1 is used for remdiv
parameter ALU_REMU  = 7'b0110010; // bit 0 is used for signed mode, bit 1 is used for remdiv
parameter ALU_REM   = 7'b0110011; // bit 0 is used for signed mode, bit 1 is used for remdiv

parameter ALU_SHUF  = 7'b0111010;
parameter ALU_SHUF2 = 7'b0111011;
parameter ALU_PCKLO = 7'b0111000;
parameter ALU_PCKHI = 7'b0111001;

// fpu
parameter ALU_FKEEP   = 7'b1111111;   // hack, to support fcvt.s.d
parameter ALU_FSGNJ   = 7'b1000000;
parameter ALU_FSGNJN  = 7'b1000001;
parameter ALU_FSGNJX  = 7'b1000010;
parameter ALU_FEQ     = 7'b1000011;
parameter ALU_FLT     = 7'b1000100;
parameter ALU_FLE     = 7'b1000101;
parameter ALU_FMAX    = 7'b1000110;
parameter ALU_FMIN    = 7'b1000111;
parameter ALU_FCLASS  = 7'b1001000;

parameter MUL_MAC32 = 3'b000;
parameter MUL_MSU32 = 3'b001;
parameter MUL_I     = 3'b010;
parameter MUL_IR    = 3'b011;
parameter MUL_DOT8  = 3'b100;
parameter MUL_DOT16 = 3'b101;
parameter MUL_H     = 3'b110;

// vector modes
parameter VEC_MODE32 = 2'b00;
parameter VEC_MODE16 = 2'b10;
parameter VEC_MODE8  = 2'b11;


  // FSM state encoding
  typedef enum  logic [4:0] { RESET, BOOT_SET, SLEEP, WAIT_SLEEP, FIRST_FETCH,
                      DECODE,
                      IRQ_TAKEN_ID, IRQ_TAKEN_IF, IRQ_FLUSH, IRQ_FLUSH_ELW, ELW_EXE,
                      FLUSH_EX, FLUSH_WB, XRET_JUMP,
                      DBG_TAKEN_ID, DBG_TAKEN_IF, DBG_FLUSH, DBG_WAIT_BRANCH } ctrl_state_e;


/////////////////////////////////////////////////////////
//    ____ ____    ____            _     _             //
//   / ___/ ___|  |  _ \ ___  __ _(_)___| |_ ___ _ __  //
//  | |   \___ \  | |_) / _ \/ _` | / __| __/ _ \ '__| //
//  | |___ ___) | |  _ <  __/ (_| | \__ \ ||  __/ |    //
//   \____|____/  |_| \_\___|\__, |_|___/\__\___|_|    //
//                           |___/                     //
/////////////////////////////////////////////////////////

// CSRs mnemonics
// imported form IBEX, some regs may be still not implemented
typedef enum logic[11:0] {
  // Machine information
  CSR_MVENDORID = 12'hF11,
  CSR_MARCHID   = 12'hF12,
  CSR_MIMPID    = 12'hF13,
  CSR_MHARTID   = 12'hF14,

  // Machine trap setup
  CSR_MSTATUS   = 12'h300,
  CSR_MISA      = 12'h301,
  CSR_MIE       = 12'h304,
  CSR_MTVEC     = 12'h305,

  // Machine trap handling
  CSR_MSCRATCH  = 12'h340,
  CSR_MEPC      = 12'h341,
  CSR_MCAUSE    = 12'h342,
  CSR_MTVAL     = 12'h343,
  CSR_MIP       = 12'h344,
  CSR_MCOUNTEREN= 12'h306,

  // User trap setup
  CSR_USTATUS   = 12'h000,
  CSR_UTVEC     = 12'h005,

  // User trap handling
  CSR_UEPC      = 12'h041,
  CSR_UCAUSE    = 12'h042,

  // Physical memory protection
  CSR_PMPCFG0   = 12'h3A0,
  CSR_PMPCFG1   = 12'h3A1,
  CSR_PMPCFG2   = 12'h3A2,
  CSR_PMPCFG3   = 12'h3A3,
  CSR_PMPADDR0  = 12'h3B0,
  CSR_PMPADDR1  = 12'h3B1,
  CSR_PMPADDR2  = 12'h3B2,
  CSR_PMPADDR3  = 12'h3B3,
  CSR_PMPADDR4  = 12'h3B4,
  CSR_PMPADDR5  = 12'h3B5,
  CSR_PMPADDR6  = 12'h3B6,
  CSR_PMPADDR7  = 12'h3B7,
  CSR_PMPADDR8  = 12'h3B8,
  CSR_PMPADDR9  = 12'h3B9,
  CSR_PMPADDR10 = 12'h3BA,
  CSR_PMPADDR11 = 12'h3BB,
  CSR_PMPADDR12 = 12'h3BC,
  CSR_PMPADDR13 = 12'h3BD,
  CSR_PMPADDR14 = 12'h3BE,
  CSR_PMPADDR15 = 12'h3BF,

  // Trigger
  CSR_TSELECT   = 12'h7A0,
  CSR_TDATA1    = 12'h7A1,
  CSR_TDATA2    = 12'h7A2,
  CSR_TDATA3    = 12'h7A3,
  CSR_TINFO     = 12'h7A4,
  CSR_MCONTEXT  = 12'h7A8,
  CSR_SCONTEXT  = 12'h7AA,

  // Debug/trace
  CSR_DCSR      = 12'h7b0,
  CSR_DPC       = 12'h7b1,

  // Debug
  CSR_DSCRATCH0 = 12'h7b2,
  CSR_DSCRATCH1 = 12'h7b3,

  // Floating Point
  CSR_FFLAGS    = 12'h001,
  CSR_FRM       = 12'h002,
  CSR_FCSR      = 12'h003,

  // Hardware Performance Monitor
  CSR_MCYCLE        = 12'hb00,
  CSR_MINSTRET      = 12'hb02,
  CSR_MHPMCOUNTER3  = 12'hb03,
  CSR_MHPMCOUNTER4  = 12'hb04,
  CSR_MHPMCOUNTER5  = 12'hb05,
  CSR_MHPMCOUNTER6  = 12'hb06,
  CSR_MHPMCOUNTER7  = 12'hb07,
  CSR_MHPMCOUNTER8  = 12'hb08,
  CSR_MHPMCOUNTER9  = 12'hb09,
  CSR_MHPMCOUNTER10 = 12'hb0a,
  CSR_MHPMCOUNTER11 = 12'hb0b,
  CSR_MHPMCOUNTER12 = 12'hb0c,
  CSR_MHPMCOUNTER13 = 12'hb0d,
  CSR_MHPMCOUNTER14 = 12'hb0e,
  CSR_MHPMCOUNTER15 = 12'hb0f,
  CSR_MHPMCOUNTER16 = 12'hb10,
  CSR_MHPMCOUNTER17 = 12'hb11,
  CSR_MHPMCOUNTER18 = 12'hb12,
  CSR_MHPMCOUNTER19 = 12'hb13,
  CSR_MHPMCOUNTER20 = 12'hb14,
  CSR_MHPMCOUNTER21 = 12'hb15,
  CSR_MHPMCOUNTER22 = 12'hb16,
  CSR_MHPMCOUNTER23 = 12'hb17,
  CSR_MHPMCOUNTER24 = 12'hb18,
  CSR_MHPMCOUNTER25 = 12'hb19,
  CSR_MHPMCOUNTER26 = 12'hb1a,
  CSR_MHPMCOUNTER27 = 12'hb1b,
  CSR_MHPMCOUNTER28 = 12'hb1c,
  CSR_MHPMCOUNTER29 = 12'hb1d,
  CSR_MHPMCOUNTER30 = 12'hb1e,
  CSR_MHPMCOUNTER31 = 12'hb1f,

  CSR_MCYCLEH        = 12'hb80,
  CSR_MINSTRETH      = 12'hb82,
  CSR_MHPMCOUNTER3H  = 12'hb83,
  CSR_MHPMCOUNTER4H  = 12'hb84,
  CSR_MHPMCOUNTER5H  = 12'hb85,
  CSR_MHPMCOUNTER6H  = 12'hb86,
  CSR_MHPMCOUNTER7H  = 12'hb87,
  CSR_MHPMCOUNTER8H  = 12'hb88,
  CSR_MHPMCOUNTER9H  = 12'hb89,
  CSR_MHPMCOUNTER10H = 12'hb8a,
  CSR_MHPMCOUNTER11H = 12'hb8b,
  CSR_MHPMCOUNTER12H = 12'hb8c,
  CSR_MHPMCOUNTER13H = 12'hb8d,
  CSR_MHPMCOUNTER14H = 12'hb8e,
  CSR_MHPMCOUNTER15H = 12'hb8f,
  CSR_MHPMCOUNTER16H = 12'hb90,
  CSR_MHPMCOUNTER17H = 12'hb91,
  CSR_MHPMCOUNTER18H = 12'hb92,
  CSR_MHPMCOUNTER19H = 12'hb93,
  CSR_MHPMCOUNTER20H = 12'hb94,
  CSR_MHPMCOUNTER21H = 12'hb95,
  CSR_MHPMCOUNTER22H = 12'hb96,
  CSR_MHPMCOUNTER23H = 12'hb97,
  CSR_MHPMCOUNTER24H = 12'hb98,
  CSR_MHPMCOUNTER25H = 12'hb99,
  CSR_MHPMCOUNTER26H = 12'hb9a,
  CSR_MHPMCOUNTER27H = 12'hb9b,
  CSR_MHPMCOUNTER28H = 12'hb9c,
  CSR_MHPMCOUNTER29H = 12'hb9d,
  CSR_MHPMCOUNTER30H = 12'hb9e,
  CSR_MHPMCOUNTER31H = 12'hb9f,

  CSR_MCOUNTINHIBIT  = 12'h320,

  CSR_MHPMEVENT3  = 12'h323,
  CSR_MHPMEVENT4  = 12'h324,
  CSR_MHPMEVENT5  = 12'h325,
  CSR_MHPMEVENT6  = 12'h326,
  CSR_MHPMEVENT7  = 12'h327,
  CSR_MHPMEVENT8  = 12'h328,
  CSR_MHPMEVENT9  = 12'h329,
  CSR_MHPMEVENT10 = 12'h32a,
  CSR_MHPMEVENT11 = 12'h32b,
  CSR_MHPMEVENT12 = 12'h32c,
  CSR_MHPMEVENT13 = 12'h32d,
  CSR_MHPMEVENT14 = 12'h32e,
  CSR_MHPMEVENT15 = 12'h32f,
  CSR_MHPMEVENT16 = 12'h330,
  CSR_MHPMEVENT17 = 12'h331,
  CSR_MHPMEVENT18 = 12'h332,
  CSR_MHPMEVENT19 = 12'h333,
  CSR_MHPMEVENT20 = 12'h334,
  CSR_MHPMEVENT21 = 12'h335,
  CSR_MHPMEVENT22 = 12'h336,
  CSR_MHPMEVENT23 = 12'h337,
  CSR_MHPMEVENT24 = 12'h338,
  CSR_MHPMEVENT25 = 12'h339,
  CSR_MHPMEVENT26 = 12'h33a,
  CSR_MHPMEVENT27 = 12'h33b,
  CSR_MHPMEVENT28 = 12'h33c,
  CSR_MHPMEVENT29 = 12'h33d,
  CSR_MHPMEVENT30 = 12'h33e,
  CSR_MHPMEVENT31 = 12'h33f

} csr_num_e;

// CSR operations
parameter CSR_OP_READ  = 2'b00;
parameter CSR_OP_WRITE = 2'b01;
parameter CSR_OP_SET   = 2'b10;
parameter CSR_OP_CLEAR = 2'b11;

// CSR interrupt pending/enable bits
parameter int unsigned CSR_MSIX_BIT      = 3;
parameter int unsigned CSR_MTIX_BIT      = 7;
parameter int unsigned CSR_MEIX_BIT      = 11;
parameter int unsigned CSR_MFIX_BIT_LOW  = 16;
parameter int unsigned CSR_MFIX_BIT_HIGH = 31;

// SPR for debugger, not accessible by CPU
parameter SP_DVR0       = 16'h3000;
parameter SP_DCR0       = 16'h3008;
parameter SP_DMR1       = 16'h3010;
parameter SP_DMR2       = 16'h3011;

parameter SP_DVR_MSB = 8'h00;
parameter SP_DCR_MSB = 8'h01;
parameter SP_DMR_MSB = 8'h02;
parameter SP_DSR_MSB = 8'h04;

// Privileged mode
typedef enum logic[1:0] {
  PRIV_LVL_M = 2'b11,
  PRIV_LVL_H = 2'b10,
  PRIV_LVL_S = 2'b01,
  PRIV_LVL_U = 2'b00
} PrivLvl_t;

// Machine Vendor ID - OpenHW JEDEC ID is '2 decimal (bank 13)'
parameter MVENDORID_OFFSET = 7'h2;      // Final byte without parity bit
parameter MVENDORID_BANK = 25'hC;       // Number of continuation codes

///////////////////////////////////////////////
//   ___ ____    ____  _                     //
//  |_ _|  _ \  / ___|| |_ __ _  __ _  ___   //
//   | || | | | \___ \| __/ _` |/ _` |/ _ \  //
//   | || |_| |  ___) | || (_| | (_| |  __/  //
//  |___|____/  |____/ \__\__,_|\__, |\___|  //
//                              |___/        //
///////////////////////////////////////////////

// forwarding operand mux
parameter SEL_REGFILE      = 2'b00;
parameter SEL_FW_EX        = 2'b01;
parameter SEL_FW_WB        = 2'b10;

// operand a selection
parameter OP_A_REGA_OR_FWD = 3'b000;
parameter OP_A_CURRPC      = 3'b001;
parameter OP_A_IMM         = 3'b010;
parameter OP_A_REGB_OR_FWD = 3'b011;
parameter OP_A_REGC_OR_FWD = 3'b100;

// immediate a selection
parameter IMMA_Z      = 1'b0;
parameter IMMA_ZERO   = 1'b1;

// operand b selection
parameter OP_B_REGB_OR_FWD = 3'b000;
parameter OP_B_REGC_OR_FWD = 3'b001;
parameter OP_B_IMM         = 3'b010;
parameter OP_B_REGA_OR_FWD = 3'b011;
parameter OP_B_BMASK       = 3'b100;

// immediate b selection
parameter IMMB_I      = 4'b0000;
parameter IMMB_S      = 4'b0001;
parameter IMMB_U      = 4'b0010;
parameter IMMB_PCINCR = 4'b0011;
parameter IMMB_S2     = 4'b0100;
parameter IMMB_S3     = 4'b0101;
parameter IMMB_VS     = 4'b0110;
parameter IMMB_VU     = 4'b0111;
parameter IMMB_SHUF   = 4'b1000;
parameter IMMB_CLIP   = 4'b1001;
parameter IMMB_BI     = 4'b1011;

// bit mask selection
parameter BMASK_A_ZERO = 1'b0;
parameter BMASK_A_S3   = 1'b1;

parameter BMASK_B_S2   = 2'b00;
parameter BMASK_B_S3   = 2'b01;
parameter BMASK_B_ZERO = 2'b10;
parameter BMASK_B_ONE  = 2'b11;

parameter BMASK_A_REG  = 1'b0;
parameter BMASK_A_IMM  = 1'b1;
parameter BMASK_B_REG  = 1'b0;
parameter BMASK_B_IMM  = 1'b1;


// multiplication immediates
parameter MIMM_ZERO    = 1'b0;
parameter MIMM_S3      = 1'b1;

// operand c selection
parameter OP_C_REGC_OR_FWD = 2'b00;
parameter OP_C_REGB_OR_FWD = 2'b01;
parameter OP_C_JT          = 2'b10;

// branch types
parameter BRANCH_NONE = 2'b00;
parameter BRANCH_JAL  = 2'b01;
parameter BRANCH_JALR = 2'b10;
parameter BRANCH_COND = 2'b11; // conditional branches

// jump target mux
parameter JT_JAL  = 2'b01;
parameter JT_JALR = 2'b10;
parameter JT_COND = 2'b11;

// Atomic operations
parameter AMO_LR   = 5'b00010;
parameter AMO_SC   = 5'b00011;
parameter AMO_SWAP = 5'b00001;
parameter AMO_ADD  = 5'b00000;
parameter AMO_XOR  = 5'b00100;
parameter AMO_AND  = 5'b01100;
parameter AMO_OR   = 5'b01000;
parameter AMO_MIN  = 5'b10000;
parameter AMO_MAX  = 5'b10100;
parameter AMO_MINU = 5'b11000;
parameter AMO_MAXU = 5'b11100;

///////////////////////////////////////////////
//   ___ _____   ____  _                     //
//  |_ _|  ___| / ___|| |_ __ _  __ _  ___   //
//   | || |_    \___ \| __/ _` |/ _` |/ _ \  //
//   | ||  _|    ___) | || (_| | (_| |  __/  //
//  |___|_|     |____/ \__\__,_|\__, |\___|  //
//                              |___/        //
///////////////////////////////////////////////

// PC mux selector defines
parameter PC_BOOT          = 3'b000;
parameter PC_JUMP          = 3'b010;
parameter PC_BRANCH        = 3'b011;
parameter PC_EXCEPTION     = 3'b100;
parameter PC_FENCEI        = 3'b001;
parameter PC_MRET          = 3'b101;
parameter PC_URET          = 3'b110;
parameter PC_DRET          = 3'b111;

// Exception PC mux selector defines
parameter EXC_PC_EXCEPTION = 3'b000;
parameter EXC_PC_IRQ       = 3'b001;

parameter EXC_PC_DBD       = 3'b010;
parameter EXC_PC_DBE       = 3'b011;

// Exception Cause
parameter EXC_CAUSE_INSTR_FAULT  = 5'h01;
parameter EXC_CAUSE_ILLEGAL_INSN = 5'h02;
parameter EXC_CAUSE_BREAKPOINT   = 5'h03;
parameter EXC_CAUSE_LOAD_FAULT   = 5'h05;
parameter EXC_CAUSE_STORE_FAULT  = 5'h07;
parameter EXC_CAUSE_ECALL_UMODE  = 5'h08;
parameter EXC_CAUSE_ECALL_MMODE  = 5'h0B;

// Interrupt mask
parameter IRQ_MASK = 32'hFFFF0888;

// Trap mux selector
parameter TRAP_MACHINE      = 2'b00;
parameter TRAP_USER         = 2'b01;

// Debug Cause
parameter DBG_CAUSE_NONE       = 3'h0;
parameter DBG_CAUSE_EBREAK     = 3'h1;
parameter DBG_CAUSE_TRIGGER    = 3'h2;
parameter DBG_CAUSE_HALTREQ    = 3'h3;
parameter DBG_CAUSE_STEP       = 3'h4;
parameter DBG_CAUSE_RSTHALTREQ = 3'h5;

// Debug module
parameter DBG_SETS_W = 6;

parameter DBG_SETS_IRQ    = 5;
parameter DBG_SETS_ECALL  = 4;
parameter DBG_SETS_EILL   = 3;
parameter DBG_SETS_ELSU   = 2;
parameter DBG_SETS_EBRK   = 1;
parameter DBG_SETS_SSTE   = 0;

parameter DBG_CAUSE_HALT   = 6'h1F;

// Constants for the dcsr.xdebugver fields
typedef enum logic[3:0] {
   XDEBUGVER_NO     = 4'd0, // no external debug support
   XDEBUGVER_STD    = 4'd4, // external debug according to RISC-V debug spec
   XDEBUGVER_NONSTD = 4'd15 // debug not conforming to RISC-V debug spec
} x_debug_ver_e;

// Trigger types
typedef enum logic [3:0] {
  TTYPE_MCONTROL = 4'h2,
  TTYPE_ICOUNT = 4'h3,
  TTYPE_ITRIGGER = 4'h4,
  TTYPE_ETRIGGER = 4'h5
} trigger_type_e;

// Floating-point extensions configuration
parameter bit C_RVF = 1'b1; // Is F extension enabled
parameter bit C_RVD = 1'b0; // Is D extension enabled - NOT SUPPORTED CURRENTLY

// Transprecision floating-point extensions configuration
parameter bit C_XF16    = 1'b0; // Is half-precision float extension (Xf16) enabled
parameter bit C_XF16ALT = 1'b0; // Is alternative half-precision float extension (Xf16alt) enabled
parameter bit C_XF8     = 1'b0; // Is quarter-precision float extension (Xf8) enabled
parameter bit C_XFVEC   = 1'b0; // Is vectorial float extension (Xfvec) enabled

// FPnew configuration
parameter C_FPNEW_OPBITS   = fpnew_pkg::OP_BITS;
parameter C_FPNEW_FMTBITS  = fpnew_pkg::FP_FORMAT_BITS;
parameter C_FPNEW_IFMTBITS = fpnew_pkg::INT_FORMAT_BITS;

// Latency of FP operations: 0 = no pipe registers, 1 = 1 pipe register etc.
parameter int unsigned C_LAT_FP64       = 'd0;
parameter int unsigned C_LAT_FP32       = 'd0;
parameter int unsigned C_LAT_FP16       = 'd0;
parameter int unsigned C_LAT_FP16ALT    = 'd0;
parameter int unsigned C_LAT_FP8        = 'd0;
parameter int unsigned C_LAT_DIVSQRT    = 'd1; // divsqrt post-processing pipe
parameter int unsigned C_LAT_CONV       = 'd0;
parameter int unsigned C_LAT_NONCOMP    = 'd0;

// General FPU-specific defines

// Length of widest floating-point format = width of fp regfile
parameter C_FLEN = C_RVD     ? 64 : // D ext.
                   C_RVF     ? 32 : // F ext.
                   C_XF16    ? 16 : // Xf16 ext.
                   C_XF16ALT ? 16 : // Xf16alt ext.
                   C_XF8     ? 8 :  // Xf8 ext.
                   0;               // Unused in case of no FP

parameter C_FFLAG             = 5;
parameter C_RM                = 3;

parameter C_PC                = 5;



/////////////////////////////////////////////////////////
//    ____ ____    ____                                //
//   / ___/ ___|  |  _ \                               //
//  | |   \___ \  | |_) |    MAPPING                   //
//  | |___ ___) | |  _ <                               //
//   \____|____/  |_| \_\                              //
//                                                     //
/////////////////////////////////////////////////////////

//Hardware Loop
parameter HWLoop0_START         = 12'h7C0; //NON standard read/write (Machine CSRs). Old address 12'h7B0;
parameter HWLoop0_END           = 12'h7C1; //NON standard read/write (Machine CSRs). Old address 12'h7B1;
parameter HWLoop0_COUNTER       = 12'h7C2; //NON standard read/write (Machine CSRs). Old address 12'h7B2;
parameter HWLoop1_START         = 12'h7C4; //NON standard read/write (Machine CSRs). Old address 12'h7B4;
parameter HWLoop1_END           = 12'h7C5; //NON standard read/write (Machine CSRs). Old address 12'h7B5;
parameter HWLoop1_COUNTER       = 12'h7C6; //NON standard read/write (Machine CSRs). Old address 12'h7B6;

//Custom Hart and Priveledge
parameter UHARTID     = 12'h014; //NON standard read/write (Machine CSRs) - User Hart ID
parameter PRIVLV      = 12'hC10; //NON standard read/write (Machine CSRs) - Privilege Level
//Custom Floating Point
parameter FPREC       = 12'h006; //NON standard read/write (Machine CSRs) - Floating Point

//PMP Range
parameter CSR_PMPADDR_RANGE_X = CSR_PMPADDR0 | 12'b0000_0000_xxxx;
parameter CSR_PMPCFG_RANGE_X  = CSR_PMPCFG0  | 12'b0000_0000_00xx;

endpackage
