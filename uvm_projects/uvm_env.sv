// Copyright 2024 ChipAgents
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// UVM Environment for CV32E40P ALU                                          //
//                                                                            //
// Description: UVM environment that instantiates and connects the ALU       //
//              agent and scoreboard for comprehensive verification           //
////////////////////////////////////////////////////////////////////////////////

`include "uvm_macros.svh"

import uvm_pkg::*;
import cv32e40p_alu_pkg::*;

// ALU Scoreboard
class alu_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(alu_scoreboard)
  
  uvm_analysis_imp #(alu_transaction, alu_scoreboard) ap_imp;
  
  int pass_count = 0;
  int fail_count = 0;
  
  function new(string name = "alu_scoreboard", uvm_component parent);
    super.new(name, parent);
    ap_imp = new("ap_imp", this);
  endfunction
  
  virtual function void write(alu_transaction trans);
    logic [31:0] expected_result;
    logic expected_comparison;
    bit is_comparison_op;
    
    // Calculate expected results based on operation
    calculate_expected(trans, expected_result, expected_comparison);
    
    // Determine if this is a comparison operation
    is_comparison_op = (trans.operator == cv32e40p_pkg::ALU_LTS  || 
                       trans.operator == cv32e40p_pkg::ALU_LTU  ||
                       trans.operator == cv32e40p_pkg::ALU_LES  ||
                       trans.operator == cv32e40p_pkg::ALU_LEU  ||
                       trans.operator == cv32e40p_pkg::ALU_GTS  ||
                       trans.operator == cv32e40p_pkg::ALU_GTU  ||
                       trans.operator == cv32e40p_pkg::ALU_GES  ||
                       trans.operator == cv32e40p_pkg::ALU_GEU  ||
                       trans.operator == cv32e40p_pkg::ALU_EQ   ||
                       trans.operator == cv32e40p_pkg::ALU_NE);
    
    // Check results based on operation type
    if (is_comparison_op) begin
      // For comparison operations, check both result and comparison_result
      if (trans.result == expected_result && trans.comparison_result == expected_comparison) begin
        pass_count++;
        `uvm_info("SCOREBOARD", $sformatf("PASS: Op=%s, A=0x%08h, B=0x%08h, Expected=0x%08h, Got=0x%08h, Comp=%b", 
                  trans.operator.name(), trans.operand_a, trans.operand_b, expected_result, trans.result, trans.comparison_result), UVM_LOW)
      end else begin
        fail_count++;
        `uvm_error("SCOREBOARD", $sformatf("FAIL: Op=%s, A=0x%08h, B=0x%08h, Expected=0x%08h, Got=0x%08h, ExpComp=%b, GotComp=%b", 
                   trans.operator.name(), trans.operand_a, trans.operand_b, expected_result, trans.result, expected_comparison, trans.comparison_result))
      end
    end else begin
      // For non-comparison operations, only check result
      if (trans.result == expected_result) begin
        pass_count++;
        `uvm_info("SCOREBOARD", $sformatf("PASS: Op=%s, A=0x%08h, B=0x%08h, Expected=0x%08h, Got=0x%08h", 
                  trans.operator.name(), trans.operand_a, trans.operand_b, expected_result, trans.result), UVM_LOW)
      end else begin
        fail_count++;
        `uvm_error("SCOREBOARD", $sformatf("FAIL: Op=%s, A=0x%08h, B=0x%08h, Expected=0x%08h, Got=0x%08h", 
                   trans.operator.name(), trans.operand_a, trans.operand_b, expected_result, trans.result))
      end
    end
  endfunction
  
  virtual function void calculate_expected(alu_transaction trans, output logic [31:0] result, output logic comparison);
    // Initialize comparison to 0 for non-comparison operations
    comparison = 1'b0;
    
    // Calculate expected result based on operation
    case (trans.operator)
      cv32e40p_pkg::ALU_ADD:  result = trans.operand_a + trans.operand_b;
      cv32e40p_pkg::ALU_SUB:  result = trans.operand_a - trans.operand_b;
      cv32e40p_pkg::ALU_AND:  result = trans.operand_a & trans.operand_b;
      cv32e40p_pkg::ALU_OR:   result = trans.operand_a | trans.operand_b;
      cv32e40p_pkg::ALU_XOR:  result = trans.operand_a ^ trans.operand_b;
      cv32e40p_pkg::ALU_SLL:  result = trans.operand_a << trans.operand_b[4:0];
      cv32e40p_pkg::ALU_SRL:  result = trans.operand_a >> trans.operand_b[4:0];
      cv32e40p_pkg::ALU_SRA:  result = $signed(trans.operand_a) >>> trans.operand_b[4:0];
      cv32e40p_pkg::ALU_LTS:  begin
        result = 32'h0;
        comparison = $signed(trans.operand_a) < $signed(trans.operand_b);
      end
      cv32e40p_pkg::ALU_LTU:  begin
        result = 32'h0;
        comparison = trans.operand_a < trans.operand_b;
      end
      cv32e40p_pkg::ALU_EQ:   begin
        result = (trans.operand_a == trans.operand_b) ? 32'hFFFFFFFF : 32'h00000000;
        comparison = (trans.operand_a == trans.operand_b);
      end
      cv32e40p_pkg::ALU_NE:   begin
        result = (trans.operand_a != trans.operand_b) ? 32'hFFFFFFFF : 32'h00000000;
        comparison = (trans.operand_a != trans.operand_b);
      end
      // Division operations
      cv32e40p_pkg::ALU_DIV:  begin
        if (trans.operand_b == 0) 
          result = 32'hFFFFFFFF; // Division by zero
        else 
          result = $signed(trans.operand_a) / $signed(trans.operand_b);
      end
      cv32e40p_pkg::ALU_DIVU: begin
        if (trans.operand_b == 0) 
          result = 32'hFFFFFFFF; // Division by zero
        else 
          result = trans.operand_a / trans.operand_b;
      end
      cv32e40p_pkg::ALU_REM:  begin
        if (trans.operand_b == 0) 
          result = trans.operand_a; // Remainder when divisor is zero
        else 
          result = $signed(trans.operand_a) % $signed(trans.operand_b);
      end
      cv32e40p_pkg::ALU_REMU: begin
        if (trans.operand_b == 0) 
          result = trans.operand_a; // Remainder when divisor is zero
        else 
          result = trans.operand_a % trans.operand_b;
      end
      // Step 2: Bit manipulation operations
      cv32e40p_pkg::ALU_BEXT: begin
        // Bit extract: extract bits from operand_a starting at operand_b position for operand_c length
        logic [4:0] pos = trans.operand_b[4:0];
        logic [4:0] len = trans.operand_c[4:0];
        result = (trans.operand_a >> pos) & ((1 << len) - 1);
      end
      cv32e40p_pkg::ALU_BEXTU: begin
        // Bit extract unsigned: similar to BEXT but unsigned
        logic [4:0] pos = trans.operand_b[4:0];
        logic [4:0] len = trans.operand_c[4:0];
        result = (trans.operand_a >> pos) & ((1 << len) - 1);
      end
      cv32e40p_pkg::ALU_BINS: begin
        // Bit insert: insert operand_c into operand_a at position operand_b
        logic [4:0] pos = trans.operand_b[4:0];
        logic [31:0] mask = 32'hFFFFFFFF << pos;
        result = (trans.operand_a & ~mask) | ((trans.operand_c << pos) & mask);
      end
      cv32e40p_pkg::ALU_BCLR: begin
        // Bit clear: clear bit at position operand_b in operand_a
        logic [4:0] pos = trans.operand_b[4:0];
        result = trans.operand_a & ~(1 << pos);
      end
      cv32e40p_pkg::ALU_BSET: begin
        // Bit set: set bit at position operand_b in operand_a
        logic [4:0] pos = trans.operand_b[4:0];
        result = trans.operand_a | (1 << pos);
      end
      cv32e40p_pkg::ALU_BREV: begin
        // Bit reverse: reverse all bits in operand_a
        for (int i = 0; i < 32; i++) begin
          result[i] = trans.operand_a[31-i];
        end
      end
      default:  begin
        result = 32'hDEADBEEF; // Placeholder for complex operations
        comparison = 1'b0;
      end
    endcase
  endfunction
  
  virtual function void report_phase(uvm_phase phase);
    `uvm_info("SCOREBOARD", $sformatf("Test Results: PASS=%0d, FAIL=%0d", pass_count, fail_count), UVM_LOW)
  endfunction
  
endclass

// ALU Environment
class alu_env extends uvm_env;
  `uvm_component_utils(alu_env)
  
  alu_agent      agent;
  alu_scoreboard scoreboard;
  
  function new(string name = "alu_env", uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    agent = alu_agent::type_id::create("agent", this);
    scoreboard = alu_scoreboard::type_id::create("scoreboard", this);
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    agent.monitor.ap.connect(scoreboard.ap_imp);
  endfunction
  
endclass