// Copyright (c) 2020 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

// Tracer package
//
// Contributors: Steve Richmond, Silicon Labs <steve.richmond@silabs.com>
//               Pascal Gouedo, Dolphin Design <pascal.gouedo@dolphin.fr>

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

  // CUSTOM_0
  parameter INSTR_BEQIMM = {17'b?, 3'b110, 5'b?, OPCODE_CUSTOM_0};
  parameter INSTR_BNEIMM = {17'b?, 3'b111, 5'b?, OPCODE_CUSTOM_0};

  // CUSTOM_1
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

  // to be used in tracer!

endpackage
