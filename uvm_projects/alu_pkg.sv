// Copyright 2024 ChipAgents
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// ALU Package for UVM Testbench                                             //
//                                                                            //
// Description: Package containing transaction class and other shared        //
//              definitions for the UVM testbench. Uses cv32e40p_pkg types.  //
////////////////////////////////////////////////////////////////////////////////

`include "uvm_macros.svh"

// Import CV32E40P package for ALU opcodes and constants
package cv32e40p_alu_pkg;
  
  import uvm_pkg::*;
  import cv32e40p_pkg::*;
  
  // ALU Transaction Class
  class alu_transaction extends uvm_sequence_item;
    
    // Input signals
    rand bit                enable;
    rand alu_opcode_e       operator;
    rand bit [31:0]         operand_a;
    rand bit [31:0]         operand_b;
    rand bit [31:0]         operand_c;
    rand bit [1:0]          vector_mode;
    rand bit [4:0]          bmask_a;
    rand bit [4:0]          bmask_b;
    rand bit [1:0]          imm_vec_ext;
    rand bit                is_clpx;
    rand bit                is_subrot;
    rand bit [1:0]          clpx_shift;
    
    // Output signals (not randomized)
    bit [31:0]              result;
    bit                     comparison_result;
    bit                     ready;
    rand bit                ex_ready;
    
    // UVM macros
    `uvm_object_utils_begin(alu_transaction)
      `uvm_field_int(enable, UVM_ALL_ON)
      `uvm_field_enum(alu_opcode_e, operator, UVM_ALL_ON)
      `uvm_field_int(operand_a, UVM_ALL_ON)
      `uvm_field_int(operand_b, UVM_ALL_ON)
      `uvm_field_int(operand_c, UVM_ALL_ON)
      `uvm_field_int(vector_mode, UVM_ALL_ON)
      `uvm_field_int(bmask_a, UVM_ALL_ON)
      `uvm_field_int(bmask_b, UVM_ALL_ON)
      `uvm_field_int(imm_vec_ext, UVM_ALL_ON)
      `uvm_field_int(is_clpx, UVM_ALL_ON)
      `uvm_field_int(is_subrot, UVM_ALL_ON)
      `uvm_field_int(clpx_shift, UVM_ALL_ON)
      `uvm_field_int(result, UVM_ALL_ON | UVM_NOCOMPARE)
      `uvm_field_int(comparison_result, UVM_ALL_ON | UVM_NOCOMPARE)
      `uvm_field_int(ready, UVM_ALL_ON | UVM_NOCOMPARE)
      `uvm_field_int(ex_ready, UVM_ALL_ON)
    `uvm_object_utils_end
    
    // Constructor
    function new(string name = "alu_transaction");
      super.new(name);
    endfunction
    
    // Constraints for reasonable randomization
    constraint valid_operation {
      operator inside {
        cv32e40p_pkg::ALU_ADD, cv32e40p_pkg::ALU_SUB, cv32e40p_pkg::ALU_ADDU, cv32e40p_pkg::ALU_SUBU,
        cv32e40p_pkg::ALU_XOR, cv32e40p_pkg::ALU_OR, cv32e40p_pkg::ALU_AND,
        cv32e40p_pkg::ALU_SRA, cv32e40p_pkg::ALU_SRL, cv32e40p_pkg::ALU_SLL,
        cv32e40p_pkg::ALU_LTS, cv32e40p_pkg::ALU_LTU, cv32e40p_pkg::ALU_EQ, cv32e40p_pkg::ALU_NE,
        cv32e40p_pkg::ALU_MIN, cv32e40p_pkg::ALU_MINU, cv32e40p_pkg::ALU_MAX, cv32e40p_pkg::ALU_MAXU,
        // Step 1: Add division operations (highest impact +15-20% coverage)
        cv32e40p_pkg::ALU_DIV, cv32e40p_pkg::ALU_DIVU, cv32e40p_pkg::ALU_REM, cv32e40p_pkg::ALU_REMU,
        // Step 2: Add bit manipulation operations (high impact +10-15% coverage)
        cv32e40p_pkg::ALU_BEXT, cv32e40p_pkg::ALU_BEXTU, cv32e40p_pkg::ALU_BINS, 
        cv32e40p_pkg::ALU_BCLR, cv32e40p_pkg::ALU_BSET, cv32e40p_pkg::ALU_BREV
      };
    }
    
    constraint valid_vector_mode {
      vector_mode inside {cv32e40p_pkg::VEC_MODE32, cv32e40p_pkg::VEC_MODE16, cv32e40p_pkg::VEC_MODE8};
    }
    
    constraint valid_shift_amount {
      if (operator inside {cv32e40p_pkg::ALU_SRA, cv32e40p_pkg::ALU_SRL, cv32e40p_pkg::ALU_SLL}) {
        operand_b[31:5] == 27'b0; // Limit shift amount to 0-31
      }
    }
    
    constraint valid_bmask {
      bmask_a < 32;
      bmask_b < 32;
    }
    
    constraint enable_mostly_on {
      enable dist {1 := 95, 0 := 5};
    }
    
    constraint ex_ready_mostly_on {
      ex_ready dist {1 := 90, 0 := 10};
    }
    
  endclass
  
endpackage