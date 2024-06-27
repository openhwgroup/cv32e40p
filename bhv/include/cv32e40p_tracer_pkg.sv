// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


package cv32e40p_tracer_pkg;
  import cv32e40p_pkg::*;

  // settings
  parameter bit SymbolicRegs = 0;  // show abi names for registers

  // instruction masks (for tracer)
  parameter INSTR_LUI = {25'b?, OPCODE_LUI};
  parameter INSTR_AUIPC = {25'b?, OPCODE_AUIPC};
  parameter INSTR_JAL = {25'b?, OPCODE_JAL};
  parameter INSTR_JALR = {17'b?, 3'b000, 5'b?, OPCODE_JALR};
  // BRANCH
  parameter INSTR_BEQ = {17'b?, 3'b000, 5'b?, OPCODE_BRANCH};
  parameter INSTR_BNE = {17'b?, 3'b001, 5'b?, OPCODE_BRANCH};
  parameter INSTR_BLT = {17'b?, 3'b100, 5'b?, OPCODE_BRANCH};
  parameter INSTR_BGE = {17'b?, 3'b101, 5'b?, OPCODE_BRANCH};
  parameter INSTR_BLTU = {17'b?, 3'b110, 5'b?, OPCODE_BRANCH};
  parameter INSTR_BGEU = {17'b?, 3'b111, 5'b?, OPCODE_BRANCH};
  // OPIMM
  parameter INSTR_ADDI = {17'b?, 3'b000, 5'b?, OPCODE_OPIMM};
  parameter INSTR_SLTI = {17'b?, 3'b010, 5'b?, OPCODE_OPIMM};
  parameter INSTR_SLTIU = {17'b?, 3'b011, 5'b?, OPCODE_OPIMM};
  parameter INSTR_XORI = {17'b?, 3'b100, 5'b?, OPCODE_OPIMM};
  parameter INSTR_ORI = {17'b?, 3'b110, 5'b?, OPCODE_OPIMM};
  parameter INSTR_ANDI = {17'b?, 3'b111, 5'b?, OPCODE_OPIMM};
  parameter INSTR_SLLI = {7'b0000000, 10'b?, 3'b001, 5'b?, OPCODE_OPIMM};
  parameter INSTR_SRLI = {7'b0000000, 10'b?, 3'b101, 5'b?, OPCODE_OPIMM};
  parameter INSTR_SRAI = {7'b0100000, 10'b?, 3'b101, 5'b?, OPCODE_OPIMM};
  // OP
  parameter INSTR_ADD = {7'b0000000, 10'b?, 3'b000, 5'b?, OPCODE_OP};
  parameter INSTR_SUB = {7'b0100000, 10'b?, 3'b000, 5'b?, OPCODE_OP};
  parameter INSTR_SLL = {7'b0000000, 10'b?, 3'b001, 5'b?, OPCODE_OP};
  parameter INSTR_SLT = {7'b0000000, 10'b?, 3'b010, 5'b?, OPCODE_OP};
  parameter INSTR_SLTU = {7'b0000000, 10'b?, 3'b011, 5'b?, OPCODE_OP};
  parameter INSTR_XOR = {7'b0000000, 10'b?, 3'b100, 5'b?, OPCODE_OP};
  parameter INSTR_SRL = {7'b0000000, 10'b?, 3'b101, 5'b?, OPCODE_OP};
  parameter INSTR_SRA = {7'b0100000, 10'b?, 3'b101, 5'b?, OPCODE_OP};
  parameter INSTR_OR = {7'b0000000, 10'b?, 3'b110, 5'b?, OPCODE_OP};
  parameter INSTR_AND = {7'b0000000, 10'b?, 3'b111, 5'b?, OPCODE_OP};

  parameter INSTR_PAVG = {7'b0000010, 10'b?, 3'b000, 5'b?, OPCODE_OP};
  parameter INSTR_PAVGU = {7'b0000010, 10'b?, 3'b001, 5'b?, OPCODE_OP};

  // FENCE
  parameter INSTR_FENCE = {4'b0, 8'b?, 13'b0, OPCODE_FENCE};
  parameter INSTR_FENCEI = {17'b0, 3'b001, 5'b0, OPCODE_FENCE};
  // SYSTEM
  parameter INSTR_CSRRW = {17'b?, 3'b001, 5'b?, OPCODE_SYSTEM};
  parameter INSTR_CSRRS = {17'b?, 3'b010, 5'b?, OPCODE_SYSTEM};
  parameter INSTR_CSRRC = {17'b?, 3'b011, 5'b?, OPCODE_SYSTEM};
  parameter INSTR_CSRRWI = {17'b?, 3'b101, 5'b?, OPCODE_SYSTEM};
  parameter INSTR_CSRRSI = {17'b?, 3'b110, 5'b?, OPCODE_SYSTEM};
  parameter INSTR_CSRRCI = {17'b?, 3'b111, 5'b?, OPCODE_SYSTEM};
  parameter INSTR_ECALL = {12'b000000000000, 13'b0, OPCODE_SYSTEM};
  parameter INSTR_EBREAK = {12'b000000000001, 13'b0, OPCODE_SYSTEM};
  parameter INSTR_URET = {12'b000000000010, 13'b0, OPCODE_SYSTEM};
  parameter INSTR_SRET = {12'b000100000010, 13'b0, OPCODE_SYSTEM};
  parameter INSTR_MRET = {12'b001100000010, 13'b0, OPCODE_SYSTEM};
  parameter INSTR_DRET = {12'b011110110010, 13'b0, OPCODE_SYSTEM};
  parameter INSTR_WFI = {12'b000100000101, 13'b0, OPCODE_SYSTEM};

  // RV32M
  parameter INSTR_DIV = {7'b0000001, 10'b?, 3'b100, 5'b?, OPCODE_OP};
  parameter INSTR_DIVU = {7'b0000001, 10'b?, 3'b101, 5'b?, OPCODE_OP};
  parameter INSTR_REM = {7'b0000001, 10'b?, 3'b110, 5'b?, OPCODE_OP};
  parameter INSTR_REMU = {7'b0000001, 10'b?, 3'b111, 5'b?, OPCODE_OP};
  parameter INSTR_PMUL = {7'b0000001, 10'b?, 3'b000, 5'b?, OPCODE_OP};
  parameter INSTR_PMUH = {7'b0000001, 10'b?, 3'b001, 5'b?, OPCODE_OP};
  parameter INSTR_PMULHSU = {7'b0000001, 10'b?, 3'b010, 5'b?, OPCODE_OP};
  parameter INSTR_PMULHU = {7'b0000001, 10'b?, 3'b011, 5'b?, OPCODE_OP};

  // RV32F
  parameter INSTR_FMADD = {5'b?, 2'b00, 10'b?, 3'b?, 5'b?, OPCODE_OP_FMADD};
  parameter INSTR_FMSUB = {5'b?, 2'b00, 10'b?, 3'b?, 5'b?, OPCODE_OP_FMSUB};
  parameter INSTR_FNMSUB = {5'b?, 2'b00, 10'b?, 3'b?, 5'b?, OPCODE_OP_FNMSUB};
  parameter INSTR_FNMADD = {5'b?, 2'b00, 10'b?, 3'b?, 5'b?, OPCODE_OP_FNMADD};

  parameter INSTR_FADD = {5'b00000, 2'b00, 10'b?, 3'b?, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FSUB = {5'b00001, 2'b00, 10'b?, 3'b?, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FMUL = {5'b00010, 2'b00, 10'b?, 3'b?, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FDIV = {5'b00011, 2'b00, 10'b?, 3'b?, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FSQRT = {5'b01011, 2'b00, 5'b0, 5'b?, 3'b?, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FSGNJS = {5'b00100, 2'b00, 10'b?, 3'b000, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FSGNJNS = {5'b00100, 2'b00, 10'b?, 3'b001, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FSGNJXS = {5'b00100, 2'b00, 10'b?, 3'b010, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FMIN = {5'b00101, 2'b00, 10'b?, 3'b000, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FMAX = {5'b00101, 2'b00, 10'b?, 3'b001, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FCVTWS = {5'b11000, 2'b00, 5'b0, 5'b?, 3'b?, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FCVTWUS = {5'b11000, 2'b00, 5'b1, 5'b?, 3'b?, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FMVXS = {5'b11100, 2'b00, 5'b0, 5'b?, 3'b000, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FEQS = {5'b10100, 2'b00, 10'b?, 3'b010, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FLTS = {5'b10100, 2'b00, 10'b?, 3'b001, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FLES = {5'b10100, 2'b00, 10'b?, 3'b000, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FCLASS = {5'b11100, 2'b00, 5'b0, 5'b?, 3'b001, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FCVTSW = {5'b11010, 2'b00, 5'b0, 5'b?, 3'b?, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FCVTSWU = {5'b11010, 2'b00, 5'b1, 5'b?, 3'b?, 5'b?, OPCODE_OP_FP};
  parameter INSTR_FMVSX = {5'b11110, 2'b00, 5'b0, 5'b?, 3'b000, 5'b?, OPCODE_OP_FP};

  // RV32A
  parameter INSTR_LR = {AMO_LR, 2'b?, 5'b0, 5'b?, 3'b010, 5'b?, OPCODE_AMO};
  parameter INSTR_SC = {AMO_SC, 2'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_AMO};
  parameter INSTR_AMOSWAP = {AMO_SWAP, 2'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_AMO};
  parameter INSTR_AMOADD = {AMO_ADD, 2'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_AMO};
  parameter INSTR_AMOXOR = {AMO_XOR, 2'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_AMO};
  parameter INSTR_AMOAND = {AMO_AND, 2'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_AMO};
  parameter INSTR_AMOOR = {AMO_OR, 2'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_AMO};
  parameter INSTR_AMOMIN = {AMO_MIN, 2'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_AMO};
  parameter INSTR_AMOMAX = {AMO_MAX, 2'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_AMO};
  parameter INSTR_AMOMINU = {AMO_MINU, 2'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_AMO};
  parameter INSTR_AMOMAXU = {AMO_MAXU, 2'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_AMO};


  // LOAD STORE
  parameter INSTR_LB = {17'b?, 3'b000, 5'b?, OPCODE_LOAD};
  parameter INSTR_LH = {17'b?, 3'b001, 5'b?, OPCODE_LOAD};
  parameter INSTR_LW = {17'b?, 3'b010, 5'b?, OPCODE_LOAD};
  parameter INSTR_LBU = {17'b?, 3'b100, 5'b?, OPCODE_LOAD};
  parameter INSTR_LHU = {17'b?, 3'b101, 5'b?, OPCODE_LOAD};

  parameter INSTR_SB = {17'b?, 3'b000, 5'b?, OPCODE_STORE};
  parameter INSTR_SH = {17'b?, 3'b001, 5'b?, OPCODE_STORE};
  parameter INSTR_SW = {17'b?, 3'b010, 5'b?, OPCODE_STORE};

  // parameter INSTR_FL  = {OPCODE_LOAD_FP};
  // parameter INSTR_FS  = {OPCODE_STORE_FP}

  // CUSTOM_0
  parameter INSTR_BEQIMM = {17'b?, 3'b110, 5'b?, OPCODE_CUSTOM_0};
  parameter INSTR_BNEIMM = {17'b?, 3'b111, 5'b?, OPCODE_CUSTOM_0};

  // Post-Increment Register-Immediate Load
  parameter INSTR_CVLBI = {17'b?, 3'b000, 5'b?, OPCODE_CUSTOM_0};
  parameter INSTR_CVLBUI = {17'b?, 3'b100, 5'b?, OPCODE_CUSTOM_0};
  parameter INSTR_CVLHI = {17'b?, 3'b001, 5'b?, OPCODE_CUSTOM_0};
  parameter INSTR_CVLHUI = {17'b?, 3'b101, 5'b?, OPCODE_CUSTOM_0};
  parameter INSTR_CVLWI = {17'b?, 3'b010, 5'b?, OPCODE_CUSTOM_0};

  // Event Load
  parameter INSTR_CVELW = {17'b?, 3'b011, 5'b?, OPCODE_CUSTOM_0};

  // CUSTOM_1
  // Post-Increment Register-Register Load
  parameter INSTR_CVLBR = {7'b0000000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVLBUR = {7'b0001000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVLHR = {7'b0000001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVLHUR = {7'b0001001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVLWR = {7'b0000010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  // Register-Register Load
  parameter INSTR_CVLBRR = {7'b0000100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVLBURR = {7'b0001100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVLHRR = {7'b0000101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVLHURR = {7'b0001101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVLWRR = {7'b0000110, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  // Post-Increment Register-Immediate Store
  parameter INSTR_CVSBI = {17'b?, 3'b000, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVSHI = {17'b?, 3'b001, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVSWI = {17'b?, 3'b010, 5'b?, OPCODE_CUSTOM_1};

  // Post-Increment Register-Register Store operations encoding
  parameter INSTR_CVSBR = {7'b0010000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVSHR = {7'b0010001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVSWR = {7'b0010010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  // Register-Register Store operations
  parameter INSTR_CVSBRR = {7'b0010100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVSHRR = {7'b0010101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CVSWRR = {7'b0010110, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  // Hardware Loops
  parameter INSTR_CVSTARTI0 = {12'b?, 5'b00000, 3'b100, 4'b0000, 1'b0, OPCODE_CUSTOM_1};
  parameter INSTR_CVSTART0 = {12'b000000000000, 5'b?, 3'b100, 4'b0001, 1'b0, OPCODE_CUSTOM_1};
  parameter INSTR_CVSENDI0 = {12'b?, 5'b00000, 3'b100, 4'b0010, 1'b0, OPCODE_CUSTOM_1};
  parameter INSTR_CVEND0 = {12'b000000000000, 5'b?, 3'b100, 4'b0011, 1'b0, OPCODE_CUSTOM_1};
  parameter INSTR_CVCOUNTI0 = {12'b?, 5'b00000, 3'b100, 4'b0100, 1'b0, OPCODE_CUSTOM_1};
  parameter INSTR_CVCOUNT0 = {12'b000000000000, 5'b?, 3'b100, 4'b0101, 1'b0, OPCODE_CUSTOM_1};
  parameter INSTR_CVSETUPI0 = {17'b?, 3'b100, 4'b0110, 1'b0, OPCODE_CUSTOM_1};
  parameter INSTR_CVSETUP0 = {12'b?, 5'b?, 3'b100, 4'b0111, 1'b0, OPCODE_CUSTOM_1};

  parameter INSTR_CVSTARTI1 = {12'b?, 5'b00000, 3'b100, 4'b0000, 1'b1, OPCODE_CUSTOM_1};
  parameter INSTR_CVSTART1 = {12'b000000000000, 5'b?, 3'b100, 4'b0001, 1'b1, OPCODE_CUSTOM_1};
  parameter INSTR_CVSENDI1 = {12'b?, 5'b00000, 3'b100, 4'b0010, 1'b1, OPCODE_CUSTOM_1};
  parameter INSTR_CVEND1 = {12'b000000000000, 5'b?, 3'b100, 4'b0011, 1'b1, OPCODE_CUSTOM_1};
  parameter INSTR_CVCOUNTI1 = {12'b?, 5'b00000, 3'b100, 4'b0100, 1'b1, OPCODE_CUSTOM_1};
  parameter INSTR_CVCOUNT1 = {12'b000000000000, 5'b?, 3'b100, 4'b0101, 1'b1, OPCODE_CUSTOM_1};
  parameter INSTR_CVSETUPI1 = {17'b?, 3'b100, 4'b0110, 1'b1, OPCODE_CUSTOM_1};
  parameter INSTR_CVSETUP1 = {12'b?, 5'b?, 3'b100, 4'b0111, 1'b1, OPCODE_CUSTOM_1};


  parameter INSTR_FF1 = {7'b0100001, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_FL1 = {7'b0100010, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CLB = {7'b0100011, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_CNT = {7'b0100100, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  parameter INSTR_EXTHS = {7'b0110000, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_EXTHZ = {7'b0110001, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_EXTBS = {7'b0110010, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_EXTBZ = {7'b0110011, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  parameter INSTR_PADDNR = {7'b1000000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PADDUNR = {7'b1000001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PADDRNR = {7'b1000010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PADDURNR = {7'b1000011, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PSUBNR = {7'b1000100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PSUBUNR = {7'b1000101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PSUBRNR = {7'b1000110, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PSUBURNR = {7'b1000111, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  parameter INSTR_PABS = {7'b0101000, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PCLIP = {7'b0111000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PCLIPU = {7'b0111001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PCLIPR = {7'b0111010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PCLIPUR = {7'b0111011, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  parameter INSTR_PSLET = {7'b0101001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PSLETU = {7'b0101010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PMIN = {7'b0101011, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PMINU = {7'b0101100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PMAX = {7'b0101101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PMAXU = {7'b0101110, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_ROR = {7'b0100000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  parameter INSTR_PBEXTR = {7'b0011000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PBEXTUR = {7'b0011001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PBINSR = {7'b0011010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PBCLRR = {7'b0011100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PBSETR = {7'b0011101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  parameter INSTR_PMAC = {7'b1001000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
  parameter INSTR_PMSU = {7'b1001001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

  // CUSTOM_2
  parameter INSTR_PBEXT = {2'b00, 5'b?, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PBEXTU = {2'b01, 5'b?, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PBINS = {2'b10, 5'b?, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PBCLR = {2'b00, 5'b?, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PBSET = {2'b01, 5'b?, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PBREV = {2'b11, 5'b?, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_2};

  parameter INSTR_PADDN = {2'b00, 15'b?, 3'b010, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PADDUN = {2'b01, 15'b?, 3'b010, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PADDRN = {2'b10, 15'b?, 3'b010, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PADDURN = {2'b11, 15'b?, 3'b010, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PSUBN = {2'b00, 15'b?, 3'b011, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PSUBUN = {2'b01, 15'b?, 3'b011, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PSUBRN = {2'b10, 15'b?, 3'b011, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PSUBURN = {2'b11, 15'b?, 3'b011, 5'b?, OPCODE_CUSTOM_2};

  parameter INSTR_PMULSN = {2'b00, 5'b?, 10'b?, 3'b100, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMULHHSN = {2'b01, 5'b?, 10'b?, 3'b100, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMULSRN = {2'b10, 5'b?, 10'b?, 3'b100, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMULHHSRN = {2'b11, 5'b?, 10'b?, 3'b100, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMULUN = {2'b00, 5'b?, 10'b?, 3'b101, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMULHHUN = {2'b01, 5'b?, 10'b?, 3'b101, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMULURN = {2'b10, 5'b?, 10'b?, 3'b101, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMULHHURN = {2'b11, 5'b?, 10'b?, 3'b101, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMACSN = {2'b00, 5'b?, 10'b?, 3'b110, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMACHHSN = {2'b01, 5'b?, 10'b?, 3'b110, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMACSRN = {2'b10, 5'b?, 10'b?, 3'b110, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMACHHSRN = {2'b11, 5'b?, 10'b?, 3'b110, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMACUN = {2'b00, 5'b?, 10'b?, 3'b111, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMACHHUN = {2'b01, 5'b?, 10'b?, 3'b111, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMACURN = {2'b10, 5'b?, 10'b?, 3'b111, 5'b?, OPCODE_CUSTOM_2};
  parameter INSTR_PMACHHURN = {2'b11, 5'b?, 10'b?, 3'b111, 5'b?, OPCODE_CUSTOM_2};


  // CUSTOM_3
  // SIMD ALU
  parameter INSTR_CVADDH = {5'b00000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVADDSCH = {5'b00000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVADDSCIH = {5'b00000, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVADDB = {5'b00000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVADDSCB = {5'b00000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVADDSCIB = {5'b00000, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVSUBH = {5'b00001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSUBSCH = {5'b00001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSUBSCIH = {5'b00001, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSUBB = {5'b00001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSUBSCB = {5'b00001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSUBSCIB = {5'b00001, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVAVGH = {5'b00010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVAVGSCH = {5'b00010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVAVGSCIH = {5'b00010, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVAVGB = {5'b00010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVAVGSCB = {5'b00010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVAVGSCIB = {5'b00010, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVAVGUH = {5'b00011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVAVGUSCH = {5'b00011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVAVGUSCIH = {5'b00011, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVAVGUB = {5'b00011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVAVGUSCB = {5'b00011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVAVGUSCIB = {5'b00011, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVMINH = {5'b00100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMINSCH = {5'b00100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMINSCIH = {5'b00100, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMINB = {5'b00100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMINSCB = {5'b00100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMINSCIB = {5'b00100, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVMINUH = {5'b00101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMINUSCH = {5'b00101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMINUSCIH = {5'b00101, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMINUB = {5'b00101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMINUSCB = {5'b00101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMINUSCIB = {5'b00101, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVMAXH = {5'b00110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMAXSCH = {5'b00110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMAXSCIH = {5'b00110, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMAXB = {5'b00110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMAXSCB = {5'b00110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMAXSCIB = {5'b00110, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVMAXUH = {5'b00111, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMAXUSCH = {5'b00111, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMAXUSCIH = {5'b00111, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMAXUB = {5'b00111, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMAXUSCB = {5'b00111, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVMAXUSCIB = {5'b00111, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVSRLH = {5'b01000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSRLSCH = {5'b01000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSRLSCIH = {5'b01000, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSRLB = {5'b01000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSRLSCB = {5'b01000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSRLSCIB = {5'b01000, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVSRAH = {5'b01001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSRASCH = {5'b01001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSRASCIH = {5'b01001, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSRAB = {5'b01001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSRASCB = {5'b01001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSRASCIB = {5'b01001, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVSLLH = {5'b01010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSLLSCH = {5'b01010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSLLSCIH = {5'b01010, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSLLB = {5'b01010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSLLSCB = {5'b01010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSLLSCIB = {5'b01010, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVORH = {5'b01011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVORSCH = {5'b01011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVORSCIH = {5'b01011, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVORB = {5'b01011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVORSCB = {5'b01011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVORSCIB = {5'b01011, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVXORH = {5'b01100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVXORSCH = {5'b01100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVXORSCIH = {5'b01100, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVXORB = {5'b01100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVXORSCB = {5'b01100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVXORSCIB = {5'b01100, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVANDH = {5'b01101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVANDSCH = {5'b01101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVANDSCIH = {5'b01101, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVANDB = {5'b01101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVANDSCB = {5'b01101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVANDSCIB = {5'b01101, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVABSH = {5'b01110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVABSB = {5'b01110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVEXTRACTH = {5'b10111, 1'b0, 6'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVEXTRACTB = {5'b10111, 1'b0, 6'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVEXTRACTUH = {5'b10111, 1'b0, 6'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVEXTRACTUB = {5'b10111, 1'b0, 6'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVINSERTH = {5'b10111, 1'b0, 6'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVINSERTB = {5'b10111, 1'b0, 6'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVDOTUPH = {5'b10000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTUPSCH = {5'b10000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTUPSCIH = {5'b10000, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTUPB = {5'b10000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTUPSCB = {5'b10000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTUPSCIB = {5'b10000, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVDOTUSPH = {5'b10001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTUSPSCH = {5'b10001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTUSPSCIH = {5'b10001, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTUSPB = {5'b10001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTUSPSCB = {5'b10001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTUSPSCIB = {5'b10001, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVDOTSPH = {5'b10010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTSPSCH = {5'b10010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTSPSCIH = {5'b10010, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTSPB = {5'b10010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTSPSCB = {5'b10010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVDOTSPSCIB = {5'b10010, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVSDOTUPH = {5'b10011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTUPSCH = {5'b10011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTUPSCIH = {5'b10011, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTUPB = {5'b10011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTUPSCB = {5'b10011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTUPSCIB = {5'b10011, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVSDOTUSPH = {5'b10100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTUSPSCH = {5'b10100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTUSPSCIH = {5'b10100, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTUSPB = {5'b10100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTUSPSCB = {5'b10100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTUSPSCIB = {5'b10100, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVSDOTSPH = {5'b10101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTSPSCH = {5'b10101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTSPSCIH = {5'b10101, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTSPB = {5'b10101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTSPSCB = {5'b10101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSDOTSPSCIB = {5'b10101, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVSHUFFLEH = {5'b11000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSHUFFLESCIH = {5'b11000, 1'b0, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSHUFFLEB = {5'b11000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSHUFFLEL0SCIB = {5'b11000, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSHUFFLEL1SCIB = {5'b11001, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSHUFFLEL2SCIB = {5'b11010, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSHUFFLEL3SCIB = {5'b11011, 1'b0, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVSHUFFLE2H = {5'b11100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSHUFFLE2B = {5'b11100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVPACK = {5'b11110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVPACKH = {5'b11110, 1'b0, 1'b1, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVPACKHIB = {5'b11111, 1'b0, 1'b1, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVPACKLOB = {5'b11111, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};

  // SIMD COMPARISON
  parameter INSTR_CVCMPEQH = {5'b00000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPEQSCH = {5'b00000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPEQSCIH = {5'b00000, 1'b1, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPEQB = {5'b00000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPEQSCB = {5'b00000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPEQSCIB = {5'b00000, 1'b1, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVCMPNEH = {5'b00001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPNESCH = {5'b00001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPNESCIH = {5'b00001, 1'b1, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPNEB = {5'b00001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPNESCB = {5'b00001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPNESCIB = {5'b00001, 1'b1, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVCMPGTH = {5'b00010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGTSCH = {5'b00010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGTSCIH = {5'b00010, 1'b1, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGTB = {5'b00010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGTSCB = {5'b00010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGTSCIB = {5'b00010, 1'b1, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVCMPGEH = {5'b00011, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGESCH = {5'b00011, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGESCIH = {5'b00011, 1'b1, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGEB = {5'b00011, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGESCB = {5'b00011, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGESCIB = {5'b00011, 1'b1, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVCMPLTH = {5'b00100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLTSCH = {5'b00100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLTSCIH = {5'b00100, 1'b1, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLTB = {5'b00100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLTSCB = {5'b00100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLTSCIB = {5'b00100, 1'b1, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVCMPLEH = {5'b00101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLESCH = {5'b00101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLESCIH = {5'b00101, 1'b1, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLEB = {5'b00101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLESCB = {5'b00101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLESCIB = {5'b00101, 1'b1, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVCMPGTUH = {5'b00110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGTUSCH = {5'b00110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGTUSCIH = {5'b00110, 1'b1, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGTUB = {5'b00110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGTUSCB = {5'b00110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGTUSCIB = {5'b00110, 1'b1, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVCMPGEUH = {5'b00111, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGEUSCH = {5'b00111, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGEUSCIH = {5'b00111, 1'b1, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGEUB = {5'b00111, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGEUSCB = {5'b00111, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPGEUSCIB = {5'b00111, 1'b1, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVCMPLTUH = {5'b01000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLTUSCH = {5'b01000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLTUSCIH = {5'b01000, 1'b1, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLTUB = {5'b01000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLTUSCB = {5'b01000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLTUSCIB = {5'b01000, 1'b1, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVCMPLEUH = {5'b01001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLEUSCH = {5'b01001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLEUSCIH = {5'b01001, 1'b1, 6'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLEUB = {5'b01001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLEUSCB = {5'b01001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCMPLEUSCIB = {5'b01001, 1'b1, 6'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

  // SIMD CPLX
  parameter INSTR_CVCPLXMULR = {5'b01010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCPLXMULRDIV2 = {
    5'b01010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3
  };
  parameter INSTR_CVCPLXMULRDIV4 = {
    5'b01010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3
  };
  parameter INSTR_CVCPLXMULRDIV8 = {
    5'b01010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3
  };

  parameter INSTR_CVCPLXMULI = {5'b01010, 1'b1, 1'b1, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVCPLXMULIDIV2 = {
    5'b01010, 1'b1, 1'b1, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3
  };
  parameter INSTR_CVCPLXMULIDIV4 = {
    5'b01010, 1'b1, 1'b1, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3
  };
  parameter INSTR_CVCPLXMULIDIV8 = {
    5'b01010, 1'b1, 1'b1, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3
  };

  parameter INSTR_CVCPLXCONJ = {
    5'b01011, 1'b1, 1'b0, 5'b00000, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3
  };

  parameter INSTR_CVSUBROTMJ = {5'b01100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSUBROTMJDIV2 = {
    5'b01100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3
  };
  parameter INSTR_CVSUBROTMJDIV4 = {
    5'b01100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3
  };
  parameter INSTR_CVSUBROTMJDIV8 = {
    5'b01100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3
  };

  parameter INSTR_CVADDIV2 = {5'b01101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVADDIV4 = {5'b01101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVADDIV8 = {5'b01101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};

  parameter INSTR_CVSUBIV2 = {5'b01110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSUBIV4 = {5'b01110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
  parameter INSTR_CVSUBIV8 = {5'b01110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};

  // to be used in tracer!

endpackage
