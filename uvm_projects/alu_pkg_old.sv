// Copyright 2024 ChipAgents
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// ALU Package for UVM Testbench                                             //
//                                                                            //
// Description: Package containing ALU opcodes, transaction class, and       //
//              other shared definitions for the UVM testbench               //
////////////////////////////////////////////////////////////////////////////////

`include "uvm_macros.svh"

// Import CV32E40P package for ALU opcodes and constants
package cv32e40p_alu_pkg;
  
  import uvm_pkg::*;
  
  // ALU Operation Width
  parameter ALU_OP_WIDTH = 7;
  
  // ALU Operations (subset from cv32e40p_pkg)
  typedef enum logic [ALU_OP_WIDTH-1:0] {
    ALU_ADD   = 7'b0011000,
    ALU_SUB   = 7'b0011001,
    ALU_ADDU  = 7'b0011010,
    ALU_SUBU  = 7'b0011011,
    ALU_ADDR  = 7'b0011100,
    ALU_SUBR  = 7'b0011101,
    ALU_ADDUR = 7'b0011110,
    ALU_SUBUR = 7'b0011111,
    
    ALU_XOR = 7'b0101111,
    ALU_OR  = 7'b0101110,
    ALU_AND = 7'b0010101,
    
    // Shifts
    ALU_SRA = 7'b0100100,
    ALU_SRL = 7'b0100101,
    ALU_ROR = 7'b0100110,
    ALU_SLL = 7'b0100111,
    
    // Bit manipulation
    ALU_BEXT  = 7'b0101000,
    ALU_BEXTU = 7'b0101001,
    ALU_BINS  = 7'b0101010,
    ALU_BCLR  = 7'b0101011,
    ALU_BSET  = 7'b0101100,
    ALU_BREV  = 7'b1001001,
    
    // Bit counting
    ALU_FF1 = 7'b0110110,
    ALU_FL1 = 7'b0110111,
    ALU_CNT = 7'b0110100,
    ALU_CLB = 7'b0110101,
    
    // Comparisons
    ALU_LTS = 7'b0000000,
    ALU_LTU = 7'b0000001,
    ALU_LES = 7'b0000100,
    ALU_LEU = 7'b0000101,
    ALU_GTS = 7'b0001000,
    ALU_GTU = 7'b0001001,
    ALU_GES = 7'b0001010,
    ALU_GEU = 7'b0001011,
    ALU_EQ  = 7'b0001100,
    ALU_NE  = 7'b0001101,
    
    // Min/Max
    ALU_MIN  = 7'b0010000,
    ALU_MINU = 7'b0010001,
    ALU_MAX  = 7'b0010010,
    ALU_MAXU = 7'b0010011,
    
    // Absolute/Clip
    ALU_ABS   = 7'b0010100,
    ALU_CLIP  = 7'b0010110,
    ALU_CLIPU = 7'b0010111,
    
    // Division
    ALU_DIV  = 7'b0110000,
    ALU_DIVU = 7'b0110001,
    ALU_REM  = 7'b0110010,
    ALU_REMU = 7'b0110011
  } alu_opcode_e;
  
  // Vector modes
  parameter VEC_MODE32 = 2'b00;
  parameter VEC_MODE16 = 2'b10;
  parameter VEC_MODE8  = 2'b11;
  
  // ALU Transaction Class
  class alu_transaction extends uvm_sequence_item;
    
    // Input signals
    rand logic               enable;
    rand alu_opcode_e        operator;
    rand logic        [31:0] operand_a;
    rand logic        [31:0] operand_b;
    rand logic        [31:0] operand_c;
    rand logic        [1:0]  vector_mode;
    rand logic        [4:0]  bmask_a;
    rand logic        [4:0]  bmask_b;
    rand logic        [1:0]  imm_vec_ext;
    rand logic               is_clpx;
    rand logic               is_subrot;
    rand logic        [1:0]  clpx_shift;
    rand logic               ex_ready;
    
    // Output signals (for checking)
    logic [31:0] result;
    logic        comparison_result;
    logic        ready;
    
    // Constraints
    constraint c_enable { enable dist {1 := 90, 0 := 10}; }
    constraint c_vector_mode { vector_mode dist {VEC_MODE32 := 60, VEC_MODE16 := 25, VEC_MODE8 := 15}; }
    constraint c_ex_ready { ex_ready dist {1 := 95, 0 := 5}; }
    constraint c_bmask { bmask_a inside {[0:31]}; bmask_b inside {[0:31]}; }
    constraint c_clpx_shift { clpx_shift inside {[0:3]}; }
    
    // Constraint for realistic operand values
    constraint c_operands {
      operand_a dist {32'h00000000 := 5, 32'hFFFFFFFF := 5, [32'h00000001:32'hFFFFFFFE] := 90};
      operand_b dist {32'h00000000 := 5, 32'hFFFFFFFF := 5, [32'h00000001:32'hFFFFFFFE] := 90};
      operand_c dist {32'h00000000 := 5, 32'hFFFFFFFF := 5, [32'h00000001:32'hFFFFFFFE] := 90};
    }
    
    `uvm_object_utils_begin(alu_transaction)
      `uvm_field_int(enable, UVM_ALL_ON)
      `uvm_field_enum(alu_opcode_e, operator, UVM_ALL_ON)
      `uvm_field_int(operand_a, UVM_ALL_ON | UVM_HEX)
      `uvm_field_int(operand_b, UVM_ALL_ON | UVM_HEX)
      `uvm_field_int(operand_c, UVM_ALL_ON | UVM_HEX)
      `uvm_field_int(vector_mode, UVM_ALL_ON)
      `uvm_field_int(bmask_a, UVM_ALL_ON)
      `uvm_field_int(bmask_b, UVM_ALL_ON)
      `uvm_field_int(imm_vec_ext, UVM_ALL_ON)
      `uvm_field_int(is_clpx, UVM_ALL_ON)
      `uvm_field_int(is_subrot, UVM_ALL_ON)
      `uvm_field_int(clpx_shift, UVM_ALL_ON)
      `uvm_field_int(ex_ready, UVM_ALL_ON)
      `uvm_field_int(result, UVM_ALL_ON | UVM_HEX)
      `uvm_field_int(comparison_result, UVM_ALL_ON)
      `uvm_field_int(ready, UVM_ALL_ON)
    `uvm_object_utils_end
    
    function new(string name = "alu_transaction");
      super.new(name);
    endfunction
    
  endclass
  
endpackage