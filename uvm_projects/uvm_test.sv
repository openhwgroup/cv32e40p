// Copyright 2024 ChipAgents
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// UVM Test Component for CV32E40P ALU                                       //
//                                                                            //
// Description: Comprehensive UVM test for the CV32E40P ALU module           //
//              Covers arithmetic, logical, shift, comparison, bit            //
//              manipulation, and vector operations                           //
////////////////////////////////////////////////////////////////////////////////

`include "uvm_macros.svh"

import uvm_pkg::*;

import cv32e40p_alu_pkg::*;

// Agent and environment are compiled separately





// Basic ALU Sequence
class alu_basic_sequence extends uvm_sequence #(alu_transaction);
  `uvm_object_utils(alu_basic_sequence)
  
  function new(string name = "alu_basic_sequence");
    super.new(name);
  endfunction
  
  virtual task body();
    alu_transaction req;
    
    // Test basic arithmetic operations
    for (int i = 0; i < 50; i++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operator inside {cv32e40p_pkg::ALU_ADD, cv32e40p_pkg::ALU_SUB, cv32e40p_pkg::ALU_AND, cv32e40p_pkg::ALU_OR, cv32e40p_pkg::ALU_XOR};
        enable == 1'b1;
        vector_mode == cv32e40p_pkg::VEC_MODE32;
      });
      finish_item(req);
    end
    
    // Test shift operations
    for (int i = 0; i < 30; i++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operator inside {cv32e40p_pkg::ALU_SLL, cv32e40p_pkg::ALU_SRL, cv32e40p_pkg::ALU_SRA};
        enable == 1'b1;
        operand_b[31:5] == 27'b0; // Limit shift amount
      });
      finish_item(req);
    end
    
    // Test comparison operations
    for (int i = 0; i < 30; i++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operator inside {cv32e40p_pkg::ALU_LTS, cv32e40p_pkg::ALU_LTU, cv32e40p_pkg::ALU_EQ, cv32e40p_pkg::ALU_NE};
        enable == 1'b1;
      });
      finish_item(req);
    end
  endtask
  
endclass

// ALU Interface
interface alu_interface(input logic clk, input logic rst_n);
  
  logic                         enable_i;
  cv32e40p_pkg::alu_opcode_e    operator_i;
  logic        [31:0]           operand_a_i;
  logic        [31:0]           operand_b_i;
  logic        [31:0]           operand_c_i;
  logic        [1:0]            vector_mode_i;
  logic        [4:0]            bmask_a_i;
  logic        [4:0]            bmask_b_i;
  logic        [1:0]            imm_vec_ext_i;
  logic                         is_clpx_i;
  logic                         is_subrot_i;
  logic        [1:0]            clpx_shift_i;
  logic        [31:0]           result_o;
  logic                         comparison_result_o;
  logic                         ready_o;
  logic                         ex_ready_i;
  
endinterface

// ALU Test
class alu_test extends uvm_test;
  `uvm_component_utils(alu_test)
  
  alu_env env;
  
  function new(string name = "alu_test", uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = alu_env::type_id::create("env", this);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    alu_basic_sequence seq;
    
    phase.raise_objection(this);
    
    seq = alu_basic_sequence::type_id::create("seq");
    seq.start(env.agent.sequencer);
    
    #1000; // Allow time for all operations to complete
    
    phase.drop_objection(this);
  endtask
  
endclass

// Comprehensive ALU Test using new sequences
class alu_comprehensive_test extends uvm_test;
  `uvm_component_utils(alu_comprehensive_test)
  
  alu_env env;
  
  function new(string name = "alu_comprehensive_test", uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = alu_env::type_id::create("env", this);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    alu_comprehensive_seq comp_seq;
    
    phase.raise_objection(this);
    `uvm_info("COMP_TEST", "Starting comprehensive ALU test", UVM_LOW)
    
    comp_seq = alu_comprehensive_seq::type_id::create("comp_seq");
    comp_seq.start(env.agent.sequencer);
    
    #5000; // Allow time for all comprehensive tests to complete
    `uvm_info("COMP_TEST", "Comprehensive ALU test completed", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
  
endclass

// Stress Test using random sequences
class alu_stress_test extends uvm_test;
  `uvm_component_utils(alu_stress_test)
  
  alu_env env;
  
  function new(string name = "alu_stress_test", uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = alu_env::type_id::create("env", this);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    alu_random_stress_seq stress_seq;
    
    phase.raise_objection(this);
    `uvm_info("STRESS_TEST", "Starting stress test", UVM_LOW)
    
    stress_seq = alu_random_stress_seq::type_id::create("stress_seq");
    if (!stress_seq.randomize() with {num_transactions == 1000;}) begin
      `uvm_error("STRESS_TEST", "Stress sequence randomization failed")
    end
    stress_seq.start(env.agent.sequencer);
    
    #10000; // Allow time for stress test to complete
    `uvm_info("STRESS_TEST", "Stress test completed", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
  
endclass

// Assembly-driven test using existing infrastructure
class alu_assembly_test extends uvm_test;
  `uvm_component_utils(alu_assembly_test)
  
  alu_env env;
  
  function new(string name = "alu_assembly_test", uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = alu_env::type_id::create("env", this);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    alu_high_coverage_comprehensive_seq high_cov_seq;
    
    phase.raise_objection(this);
    `uvm_info("ASM_TEST", "Starting high coverage assembly-inspired test", UVM_LOW)
    
    // Run high coverage comprehensive sequence for 70% target
    high_cov_seq = alu_high_coverage_comprehensive_seq::type_id::create("high_cov_seq");
    high_cov_seq.start(env.agent.sequencer);
    
    #15000; // Allow more time for comprehensive coverage
    `uvm_info("ASM_TEST", "High coverage assembly-inspired test completed", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
  
endclass

// Step 2: Focused Bit Manipulation Test
class alu_bit_manipulation_test extends uvm_test;
  `uvm_component_utils(alu_bit_manipulation_test)
  
  alu_env env;
  
  function new(string name = "alu_bit_manipulation_test", uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = alu_env::type_id::create("env", this);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    alu_bit_manipulation_seq bit_seq;
    alu_bit_edge_cases_seq bit_edge_seq;
    
    phase.raise_objection(this);
    `uvm_info("BIT_TEST", "Starting ALU Bit Manipulation Test", UVM_LOW)
    
    // Run bit manipulation sequences
    bit_seq = alu_bit_manipulation_seq::type_id::create("bit_seq");
    bit_seq.start(env.agent.sequencer);
    
    bit_edge_seq = alu_bit_edge_cases_seq::type_id::create("bit_edge_seq");
    bit_edge_seq.start(env.agent.sequencer);
    
    `uvm_info("BIT_TEST", "ALU Bit Manipulation Test Completed", UVM_LOW)
    phase.drop_objection(this);
  endtask
  
endclass

// Top-level testbench module
module cv32e40p_alu_tb;
  
  logic clk = 0;
  logic rst_n = 0;
  
  // Clock generation
  always #5 clk = ~clk;
  
  // Reset generation
  initial begin
    rst_n = 0;
    #100;
    rst_n = 1;
  end
  
  // Interface instantiation
  alu_interface alu_if(clk, rst_n);
  
  // DUT instantiation
  cv32e40p_alu dut (
    .clk(clk),
    .rst_n(rst_n),
    .enable_i(alu_if.enable_i),
    .operator_i(alu_if.operator_i),
    .operand_a_i(alu_if.operand_a_i),
    .operand_b_i(alu_if.operand_b_i),
    .operand_c_i(alu_if.operand_c_i),
    .vector_mode_i(alu_if.vector_mode_i),
    .bmask_a_i(alu_if.bmask_a_i),
    .bmask_b_i(alu_if.bmask_b_i),
    .imm_vec_ext_i(alu_if.imm_vec_ext_i),
    .is_clpx_i(alu_if.is_clpx_i),
    .is_subrot_i(alu_if.is_subrot_i),
    .clpx_shift_i(alu_if.clpx_shift_i),
    .result_o(alu_if.result_o),
    .comparison_result_o(alu_if.comparison_result_o),
    .ready_o(alu_if.ready_o),
    .ex_ready_i(alu_if.ex_ready_i)
  );
  
  // UVM test execution
  initial begin
    uvm_config_db#(virtual alu_interface)::set(null, "*", "vif", alu_if);
    run_test("alu_test");
  end
  
  // Waveform dumping
  initial begin
    $dumpfile("cv32e40p_alu_test.vcd");
    $dumpvars(0, cv32e40p_alu_tb);
  end
  
endmodule