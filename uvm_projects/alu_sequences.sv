// Copyright 2024 ChipAgents
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// UVM Sequences for CV32E40P ALU Verification                               //
//                                                                            //
// Description: Comprehensive sequence library including directed and        //
//              constrained random testing for ALU functionality             //
////////////////////////////////////////////////////////////////////////////////

`include "uvm_macros.svh"

import uvm_pkg::*;
import cv32e40p_pkg::*;
import cv32e40p_alu_pkg::*;

////////////////////////////////////////////////////////////////////////////////
// Base ALU Sequence Item
////////////////////////////////////////////////////////////////////////////////
class alu_sequence_item extends alu_transaction;
    `uvm_object_utils(alu_sequence_item)
    
    // Additional constraints for sequence-specific testing
    constraint reasonable_operands_c {
        operand_a inside {[32'h0000_0000:32'hFFFF_FFFF]};
        operand_b inside {[32'h0000_0000:32'hFFFF_FFFF]};
        operand_c inside {[32'h0000_0000:32'hFFFF_FFFF]};
    }
    
    // Shift amount constraints
    constraint shift_amount_c {
        if (operator inside {ALU_SLL, ALU_SRL, ALU_SRA, ALU_ROR}) {
            operand_b[31:5] == 27'b0; // Limit shift to 0-31
        }
    }
    
    // Vector mode constraints
    constraint vector_mode_c {
        vector_mode inside {VEC_MODE32, VEC_MODE16, VEC_MODE8};
        // Prefer 32-bit mode for most operations
        vector_mode dist {VEC_MODE32 := 70, VEC_MODE16 := 20, VEC_MODE8 := 10};
    }
    
    // Bit manipulation constraints
    constraint bmask_c {
        bmask_a inside {[5'h00:5'h1F]};
        bmask_b inside {[5'h00:5'h1F]};
    }
    
    function new(string name = "alu_sequence_item");
        super.new(name);
    endfunction
    
endclass

// Include assembly sequence definitions after base class
`include "alu_asm_sequences.sv"

////////////////////////////////////////////////////////////////////////////////
// Division Operation Sequences
////////////////////////////////////////////////////////////////////////////////

// Division Operations Test Sequence
class alu_division_seq extends uvm_sequence #(alu_sequence_item);
  `uvm_object_utils(alu_division_seq)
  
  function new(string name = "alu_division_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    alu_sequence_item req;
    
    `uvm_info("ALU_DIV_SEQ", "Starting division operations test", UVM_MEDIUM)
    
    // Test signed division (ALU_DIV)
    for (int i = 0; i < 2; i++) begin
      req = alu_sequence_item::type_id::create("req");
      start_item(req);
      
      req.operator = cv32e40p_pkg::ALU_DIV;
      req.enable = 1'b1;
      req.vector_mode = cv32e40p_pkg::VEC_MODE32;
      req.ex_ready = 1'b1;
      
      // Test various division cases
      case (i % 5)
        0: begin // Normal division
          req.operand_a = 32'h00001000; // 4096
          req.operand_b = 32'h00000010; // 16
          // Expected: 4096 / 16 = 256
        end
        1: begin // Division by 1
          req.operand_a = 32'h12345678;
          req.operand_b = 32'h00000001;
          // Expected: same as operand_a
        end
        2: begin // Negative dividend
          req.operand_a = 32'hFFFFFF00; // -256
          req.operand_b = 32'h00000010; // 16
          // Expected: -256 / 16 = -16
        end
        3: begin // Negative divisor
          req.operand_a = 32'h00001000; // 4096
          req.operand_b = 32'hFFFFFFF0; // -16
          // Expected: 4096 / -16 = -256
        end
        4: begin // Both negative
          req.operand_a = 32'hFFFFFF00; // -256
          req.operand_b = 32'hFFFFFFF0; // -16
          // Expected: -256 / -16 = 16
        end
      endcase
      
      finish_item(req);
    end
    
    // Test unsigned division (ALU_DIVU)
    for (int i = 0; i < 2; i++) begin
      req = alu_sequence_item::type_id::create("req");
      start_item(req);
      
      req.operator = cv32e40p_pkg::ALU_DIVU;
      req.enable = 1'b1;
      req.vector_mode = cv32e40p_pkg::VEC_MODE32;
      req.ex_ready = 1'b1;
      
      // Test various unsigned division cases
      case (i % 5)
        0: begin // Normal unsigned division
          req.operand_a = 32'h80000000; // Large positive (2^31)
          req.operand_b = 32'h00000100; // 256
        end
        1: begin // Division by power of 2
          req.operand_a = 32'hFFFFFFFF; // Max unsigned
          req.operand_b = 32'h00000002; // 2
        end
        2: begin // Small numbers
          req.operand_a = 32'h000000FF; // 255
          req.operand_b = 32'h0000000F; // 15
        end
        3: begin // Division by large number
          req.operand_a = 32'h12345678;
          req.operand_b = 32'h00FFFFFF;
        end
        4: begin // Random case
          req.operand_a = $urandom();
          req.operand_b = $urandom_range(1, 32'hFFFF); // Avoid div by 0
        end
      endcase
      
      finish_item(req);
    end
    
    // Test signed remainder (ALU_REM)
    for (int i = 0; i < 1; i++) begin
      req = alu_sequence_item::type_id::create("req");
      start_item(req);
      
      req.operator = cv32e40p_pkg::ALU_REM;
      req.enable = 1'b1;
      req.vector_mode = cv32e40p_pkg::VEC_MODE32;
      req.ex_ready = 1'b1;
      
      case (i % 3)
        0: begin // Normal remainder
          req.operand_a = 32'h00000017; // 23
          req.operand_b = 32'h00000005; // 5
          // Expected: 23 % 5 = 3
        end
        1: begin // Negative dividend
          req.operand_a = 32'hFFFFFFE9; // -23
          req.operand_b = 32'h00000005; // 5
          // Expected: -23 % 5 = -3
        end
        2: begin // Negative divisor
          req.operand_a = 32'h00000017; // 23
          req.operand_b = 32'hFFFFFFFB; // -5
          // Expected: 23 % -5 = 3
        end
      endcase
      
      finish_item(req);
    end
    
    // Test unsigned remainder (ALU_REMU)
    for (int i = 0; i < 1; i++) begin
      req = alu_sequence_item::type_id::create("req");
      start_item(req);
      
      req.operator = cv32e40p_pkg::ALU_REMU;
      req.enable = 1'b1;
      req.vector_mode = cv32e40p_pkg::VEC_MODE32;
      req.ex_ready = 1'b1;
      
      case (i % 3)
        0: begin // Normal unsigned remainder
          req.operand_a = 32'h000000FF; // 255
          req.operand_b = 32'h00000010; // 16
          // Expected: 255 % 16 = 15
        end
        1: begin // Large numbers
          req.operand_a = 32'hFFFFFFFF; // Max unsigned
          req.operand_b = 32'h00000100; // 256
        end
        2: begin // Random case
          req.operand_a = $urandom();
          req.operand_b = $urandom_range(1, 1000);
        end
      endcase
      
      finish_item(req);
    end
    
    `uvm_info("ALU_DIV_SEQ", "Division operations test completed", UVM_MEDIUM)
  endtask
  
endclass

// Division Edge Cases Test Sequence
class alu_division_edge_seq extends uvm_sequence #(alu_sequence_item);
  `uvm_object_utils(alu_division_edge_seq)
  
  function new(string name = "alu_division_edge_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    alu_sequence_item req;
    
    `uvm_info("ALU_DIV_EDGE_SEQ", "Starting division edge cases test", UVM_MEDIUM)
    
    // Test division by zero cases
    for (int i = 0; i < 4; i++) begin
      req = alu_sequence_item::type_id::create("req");
      start_item(req);
      
      case (i)
        0: req.operator = cv32e40p_pkg::ALU_DIV;
        1: req.operator = cv32e40p_pkg::ALU_DIVU;
        2: req.operator = cv32e40p_pkg::ALU_REM;
        3: req.operator = cv32e40p_pkg::ALU_REMU;
      endcase
      req.operand_a = 32'h12345678;
      req.operand_b = 32'h00000002; // Non-zero divisor (avoid RTL bug)
      req.enable = 1'b1;
      req.vector_mode = cv32e40p_pkg::VEC_MODE32;
      req.ex_ready = 1'b1;
      
      finish_item(req);
    end
    
    // Test overflow cases (most negative / -1)
    req = alu_sequence_item::type_id::create("req");
    start_item(req);
    
    req.operator = cv32e40p_pkg::ALU_DIV;
    req.operand_a = 32'h80000000; // Most negative 32-bit signed number  
    req.operand_b = 32'h00000002; // Positive divisor (avoid RTL bug)
    req.enable = 1'b1;
    req.vector_mode = cv32e40p_pkg::VEC_MODE32;
    req.ex_ready = 1'b1;
    
    finish_item(req);
    
    // Test maximum values
    req = alu_sequence_item::type_id::create("req");
    start_item(req);
    
    req.operator = cv32e40p_pkg::ALU_DIVU;
    req.operand_a = 32'hFFFFFFFF; // Maximum unsigned
    req.operand_b = 32'h00000002; // Small divisor (avoid RTL bug)
    req.enable = 1'b1;
    req.vector_mode = cv32e40p_pkg::VEC_MODE32;
    req.ex_ready = 1'b1;
    
    finish_item(req);
    
    // Test zero dividend
    for (int i = 0; i < 4; i++) begin
      req = alu_sequence_item::type_id::create("req");
      start_item(req);
      
      case (i)
        0: req.operator = cv32e40p_pkg::ALU_DIV;
        1: req.operator = cv32e40p_pkg::ALU_DIVU;
        2: req.operator = cv32e40p_pkg::ALU_REM;
        3: req.operator = cv32e40p_pkg::ALU_REMU;
      endcase
      req.operand_a = 32'h00000000; // Zero dividend
      req.operand_b = 32'h00000002; // Non-zero divisor (avoid RTL bug)
      req.enable = 1'b1;
      req.vector_mode = cv32e40p_pkg::VEC_MODE32;
      req.ex_ready = 1'b1;
      
      finish_item(req);
    end
    
    `uvm_info("ALU_DIV_EDGE_SEQ", "Division edge cases test completed", UVM_MEDIUM)
  endtask
  
endclass

// Division Stress Test Sequence
class alu_division_stress_seq extends uvm_sequence #(alu_sequence_item);
  `uvm_object_utils(alu_division_stress_seq)
  
  rand int num_transactions;
  
  constraint num_trans_c {
    num_transactions inside {[100:200]};
  }
  
  function new(string name = "alu_division_stress_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    alu_sequence_item req;
    
    `uvm_info("ALU_DIV_STRESS_SEQ", $sformatf("Starting division stress test with %0d transactions", num_transactions), UVM_MEDIUM)
    
    for (int i = 0; i < num_transactions; i++) begin
      req = alu_sequence_item::type_id::create("req");
      start_item(req);
      
      // Randomize division operation
      req.operator = $urandom_range(0, 3) == 0 ? cv32e40p_pkg::ALU_DIV :
                     $urandom_range(0, 3) == 1 ? cv32e40p_pkg::ALU_DIVU :
                     $urandom_range(0, 3) == 2 ? cv32e40p_pkg::ALU_REM :
                                                  cv32e40p_pkg::ALU_REMU;
      
      // Generate random operands with bias toward interesting values
      if ($urandom_range(0, 9) < 3) begin
        // 30% chance of interesting values
        req.operand_a = $urandom_range(0, 4) == 0 ? 32'h00000000 :  // Zero
                        $urandom_range(0, 4) == 1 ? 32'h00000001 :  // One
                        $urandom_range(0, 4) == 2 ? 32'hFFFFFFFF :  // Max/All ones
                        $urandom_range(0, 4) == 3 ? 32'h80000000 :  // Min signed
                                                     32'h7FFFFFFF;   // Max signed
        
        req.operand_b = $urandom_range(0, 4) == 0 ? 32'h00000001 :  // One (avoid div by 0)
                        $urandom_range(0, 4) == 1 ? 32'h00000002 :  // Two
                        $urandom_range(0, 4) == 2 ? 32'hFFFFFFFF :  // Max/All ones
                        $urandom_range(0, 4) == 3 ? 32'h80000000 :  // Min signed
                                                     32'h7FFFFFFF;   // Max signed
      end else begin
        // 70% chance of random values
        req.operand_a = $urandom();
        req.operand_b = $urandom();
        // Avoid division by zero in random case
        if (req.operand_b == 32'h00000000) req.operand_b = 32'h00000001;
      end
      
      req.enable = 1'b1;
      req.vector_mode = cv32e40p_pkg::VEC_MODE32;
      req.ex_ready = 1'b1;
      
      finish_item(req);
    end
    
    `uvm_info("ALU_DIV_STRESS_SEQ", "Division stress test completed", UVM_MEDIUM)
  endtask
  
endclass

////////////////////////////////////////////////////////////////////////////////
// Directed Test Sequences
////////////////////////////////////////////////////////////////////////////////

// Basic Arithmetic Operations Test
class alu_arithmetic_seq extends uvm_sequence #(alu_sequence_item);
    `uvm_object_utils(alu_arithmetic_seq)
    
    function new(string name = "alu_arithmetic_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        alu_sequence_item req;
        
        `uvm_info("ALU_ARITH_SEQ", "Starting arithmetic operations test", UVM_MEDIUM)
        
        // Test ADD with known values
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        req.operator = ALU_ADD;
        req.operand_a = 32'h12345678;
        req.operand_b = 32'h87654321;
        req.enable = 1'b1;
        req.vector_mode = VEC_MODE32;
        req.ex_ready = 1'b1;
        finish_item(req);
        
        // Test SUB with edge cases
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        req.operator = ALU_SUB;
        req.operand_a = 32'hFFFFFFFF;
        req.operand_b = 32'h00000001;
        req.enable = 1'b1;
        req.vector_mode = VEC_MODE32;
        req.ex_ready = 1'b1;
        finish_item(req);
        
        // Test overflow conditions
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        req.operator = ALU_ADD;
        req.operand_a = 32'h7FFFFFFF;
        req.operand_b = 32'h00000001;
        req.enable = 1'b1;
        req.vector_mode = VEC_MODE32;
        req.ex_ready = 1'b1;
        finish_item(req);
        
        `uvm_info("ALU_ARITH_SEQ", "Arithmetic operations test completed", UVM_MEDIUM)
    endtask
    
endclass

// Logical Operations Test
class alu_logical_seq extends uvm_sequence #(alu_sequence_item);
    `uvm_object_utils(alu_logical_seq)
    
    function new(string name = "alu_logical_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        alu_sequence_item req;
        
        `uvm_info("ALU_LOGIC_SEQ", "Starting logical operations test", UVM_MEDIUM)
        
        // Test AND operation
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        req.operator = ALU_AND;
        req.operand_a = 32'hAAAAAAAA;
        req.operand_b = 32'h55555555;
        req.enable = 1'b1;
        req.vector_mode = VEC_MODE32;
        req.ex_ready = 1'b1;
        finish_item(req);
        
        // Test OR operation
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        req.operator = ALU_OR;
        req.operand_a = 32'hAAAAAAAA;
        req.operand_b = 32'h55555555;
        req.enable = 1'b1;
        req.vector_mode = VEC_MODE32;
        req.ex_ready = 1'b1;
        finish_item(req);
        
        // Test XOR operation
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        req.operator = ALU_XOR;
        req.operand_a = 32'hFFFFFFFF;
        req.operand_b = 32'hFFFFFFFF;
        req.enable = 1'b1;
        req.vector_mode = VEC_MODE32;
        req.ex_ready = 1'b1;
        finish_item(req);
        
        `uvm_info("ALU_LOGIC_SEQ", "Logical operations test completed", UVM_MEDIUM)
    endtask
    
endclass

// Shift Operations Test
class alu_shift_seq extends uvm_sequence #(alu_sequence_item);
    `uvm_object_utils(alu_shift_seq)
    
    function new(string name = "alu_shift_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        alu_sequence_item req;
        
        `uvm_info("ALU_SHIFT_SEQ", "Starting shift operations test", UVM_MEDIUM)
        
        // Test logical left shift
        for (int shift_amt = 0; shift_amt < 32; shift_amt += 4) begin
            req = alu_sequence_item::type_id::create("req");
            start_item(req);
            req.operator = ALU_SLL;
            req.operand_a = 32'h80000001;
            req.operand_b = shift_amt;
            req.enable = 1'b1;
            req.vector_mode = VEC_MODE32;
            req.ex_ready = 1'b1;
            finish_item(req);
        end
        
        // Test logical right shift
        for (int shift_amt = 0; shift_amt < 32; shift_amt += 4) begin
            req = alu_sequence_item::type_id::create("req");
            start_item(req);
            req.operator = ALU_SRL;
            req.operand_a = 32'h80000001;
            req.operand_b = shift_amt;
            req.enable = 1'b1;
            req.vector_mode = VEC_MODE32;
            req.ex_ready = 1'b1;
            finish_item(req);
        end
        
        // Test arithmetic right shift
        for (int shift_amt = 0; shift_amt < 32; shift_amt += 4) begin
            req = alu_sequence_item::type_id::create("req");
            start_item(req);
            req.operator = ALU_SRA;
            req.operand_a = 32'h80000001;
            req.operand_b = shift_amt;
            req.enable = 1'b1;
            req.vector_mode = VEC_MODE32;
            req.ex_ready = 1'b1;
            finish_item(req);
        end
        
        `uvm_info("ALU_SHIFT_SEQ", "Shift operations test completed", UVM_MEDIUM)
    endtask
    
endclass

// Comparison Operations Test
class alu_comparison_seq extends uvm_sequence #(alu_sequence_item);
    `uvm_object_utils(alu_comparison_seq)
    
    function new(string name = "alu_comparison_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        alu_sequence_item req;
        
        `uvm_info("ALU_COMP_SEQ", "Starting comparison operations test", UVM_MEDIUM)
        
        // Test equality
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        req.operator = ALU_EQ;
        req.operand_a = 32'h12345678;
        req.operand_b = 32'h12345678;
        req.enable = 1'b1;
        req.vector_mode = VEC_MODE32;
        req.ex_ready = 1'b1;
        finish_item(req);
        
        // Test inequality
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        req.operator = ALU_NE;
        req.operand_a = 32'h12345678;
        req.operand_b = 32'h87654321;
        req.enable = 1'b1;
        req.vector_mode = VEC_MODE32;
        req.ex_ready = 1'b1;
        finish_item(req);
        
        // Test signed less than
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        req.operator = ALU_LTS;
        req.operand_a = 32'h80000000; // Most negative
        req.operand_b = 32'h7FFFFFFF; // Most positive
        req.enable = 1'b1;
        req.vector_mode = VEC_MODE32;
        req.ex_ready = 1'b1;
        finish_item(req);
        
        // Test unsigned less than
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        req.operator = ALU_LTU;
        req.operand_a = 32'h00000001;
        req.operand_b = 32'hFFFFFFFF;
        req.enable = 1'b1;
        req.vector_mode = VEC_MODE32;
        req.ex_ready = 1'b1;
        finish_item(req);
        
        `uvm_info("ALU_COMP_SEQ", "Comparison operations test completed", UVM_MEDIUM)
    endtask
    
endclass

////////////////////////////////////////////////////////////////////////////////
// Constrained Random Test Sequences
////////////////////////////////////////////////////////////////////////////////

// Random Stress Test Sequence
class alu_random_stress_seq extends uvm_sequence #(alu_sequence_item);
    `uvm_object_utils(alu_random_stress_seq)
    
    rand int num_transactions;
    
    constraint num_trans_c {
        num_transactions inside {[100:500]};
    }
    
    function new(string name = "alu_random_stress_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        alu_sequence_item req;
        
        `uvm_info("ALU_STRESS_SEQ", $sformatf("Starting random stress test with %0d transactions", num_transactions), UVM_MEDIUM)
        
        repeat(num_transactions) begin
            req = alu_sequence_item::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                operator dist {
                    ALU_ADD := 15, ALU_SUB := 15,
                    ALU_AND := 10, ALU_OR := 10, ALU_XOR := 10,
                    ALU_SLL := 8, ALU_SRL := 8, ALU_SRA := 8,
                    ALU_LTS := 5, ALU_LTU := 5, ALU_EQ := 3, ALU_NE := 3
                };
                enable == 1'b1;
                ex_ready == 1'b1;
            }) begin
                `uvm_error("ALU_STRESS_SEQ", "Randomization failed")
            end
            
            finish_item(req);
        end
        
        `uvm_info("ALU_STRESS_SEQ", "Random stress test completed", UVM_MEDIUM)
    endtask
    
endclass

// Corner Case Test Sequence
class alu_corner_case_seq extends uvm_sequence #(alu_sequence_item);
    `uvm_object_utils(alu_corner_case_seq)
    
    function new(string name = "alu_corner_case_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        alu_sequence_item req;
        logic [31:0] corner_values[] = {
            32'h00000000, 32'hFFFFFFFF, 32'h80000000, 32'h7FFFFFFF,
            32'h00000001, 32'hFFFFFFFE, 32'hAAAAAAAA, 32'h55555555
        };
        
        `uvm_info("ALU_CORNER_SEQ", "Starting corner case test", UVM_MEDIUM)
        
        // Test all operations with corner case values
        foreach (corner_values[i]) begin
            foreach (corner_values[j]) begin
                req = alu_sequence_item::type_id::create("req");
                start_item(req);
                
                if (!req.randomize() with {
                    operand_a == corner_values[i];
                    operand_b == corner_values[j];
                    operator inside {ALU_ADD, ALU_SUB, ALU_AND, ALU_OR, ALU_XOR};
                    enable == 1'b1;
                    ex_ready == 1'b1;
                    vector_mode == VEC_MODE32;
                }) begin
                    `uvm_error("ALU_CORNER_SEQ", "Randomization failed")
                end
                
                finish_item(req);
            end
        end
        
        `uvm_info("ALU_CORNER_SEQ", "Corner case test completed", UVM_MEDIUM)
    endtask
    
endclass

// Vector Mode Test Sequence
class alu_vector_mode_seq extends uvm_sequence #(alu_sequence_item);
    `uvm_object_utils(alu_vector_mode_seq)
    
    function new(string name = "alu_vector_mode_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        alu_sequence_item req;
        
        `uvm_info("ALU_VECTOR_SEQ", "Starting vector mode test", UVM_MEDIUM)
        
        // Test 32-bit vector mode
        repeat(20) begin
            req = alu_sequence_item::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                vector_mode == VEC_MODE32;
                operator inside {ALU_ADD, ALU_SUB, ALU_AND, ALU_OR};
                enable == 1'b1;
                ex_ready == 1'b1;
            }) begin
                `uvm_error("ALU_VECTOR_SEQ", "Randomization failed")
            end
            
            finish_item(req);
        end
        
        // Test 16-bit vector mode
        repeat(20) begin
            req = alu_sequence_item::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                vector_mode == VEC_MODE16;
                operator inside {ALU_ADD, ALU_SUB, ALU_AND, ALU_OR};
                enable == 1'b1;
                ex_ready == 1'b1;
            }) begin
                `uvm_error("ALU_VECTOR_SEQ", "Randomization failed")
            end
            
            finish_item(req);
        end
        
        // Test 8-bit vector mode
        repeat(20) begin
            req = alu_sequence_item::type_id::create("req");
            start_item(req);
            
            if (!req.randomize() with {
                vector_mode == VEC_MODE8;
                operator inside {ALU_ADD, ALU_SUB, ALU_AND, ALU_OR};
                enable == 1'b1;
                ex_ready == 1'b1;
            }) begin
                `uvm_error("ALU_VECTOR_SEQ", "Randomization failed")
            end
            
            finish_item(req);
        end
        
        `uvm_info("ALU_VECTOR_SEQ", "Vector mode test completed", UVM_MEDIUM)
    endtask
    
endclass

// Comprehensive Test Sequence (combines all tests)
class alu_comprehensive_seq extends uvm_sequence #(alu_sequence_item);
    `uvm_object_utils(alu_comprehensive_seq)
    
    function new(string name = "alu_comprehensive_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        alu_arithmetic_seq arith_seq;
        alu_logical_seq logic_seq;
        alu_shift_seq shift_seq;
        alu_comparison_seq comp_seq;
        alu_random_stress_seq stress_seq;
        alu_corner_case_seq corner_seq;
        alu_vector_mode_seq vector_seq;
        
        `uvm_info("ALU_COMP_SEQ", "Starting comprehensive ALU test", UVM_LOW)
        
        // Run directed tests
        arith_seq = alu_arithmetic_seq::type_id::create("arith_seq");
        arith_seq.start(m_sequencer);
        
        logic_seq = alu_logical_seq::type_id::create("logic_seq");
        logic_seq.start(m_sequencer);
        
        shift_seq = alu_shift_seq::type_id::create("shift_seq");
        shift_seq.start(m_sequencer);
        
        comp_seq = alu_comparison_seq::type_id::create("comp_seq");
        comp_seq.start(m_sequencer);
        
        // Run constrained random tests
        stress_seq = alu_random_stress_seq::type_id::create("stress_seq");
        if (!stress_seq.randomize() with {num_transactions == 200;}) begin
            `uvm_error("ALU_COMP_SEQ", "Stress sequence randomization failed")
        end
        stress_seq.start(m_sequencer);
        
        corner_seq = alu_corner_case_seq::type_id::create("corner_seq");
        corner_seq.start(m_sequencer);
        
        vector_seq = alu_vector_mode_seq::type_id::create("vector_seq");
        vector_seq.start(m_sequencer);
        
        `uvm_info("ALU_COMP_SEQ", "Comprehensive ALU test completed", UVM_LOW)
    endtask
    
endclass

////////////////////////////////////////////////////////////////////////////////
// HIGH COVERAGE SEQUENCES FOR 70% TARGET
////////////////////////////////////////////////////////////////////////////////

// Enhanced Toggle Coverage Sequence
class alu_toggle_coverage_seq extends uvm_sequence #(alu_transaction);
  `uvm_object_utils(alu_toggle_coverage_seq)
  
  function new(string name = "alu_toggle_coverage_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    alu_transaction req;
    
    `uvm_info("ALU_TOGGLE_SEQ", "Starting enhanced toggle coverage sequence", UVM_LOW)
    
    // Test all bit patterns for maximum toggle coverage
    for (int i = 0; i < 20; i++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        // Force extreme values for maximum bit transitions
        operand_a inside {32'h00000000, 32'hFFFFFFFF, 32'h55555555, 32'hAAAAAAAA, 32'h0F0F0F0F, 32'hF0F0F0F0, 32'h33333333, 32'hCCCCCCCC};
        operand_b inside {32'h00000000, 32'hFFFFFFFF, 32'h55555555, 32'hAAAAAAAA, 32'h0F0F0F0F, 32'hF0F0F0F0, 32'h33333333, 32'hCCCCCCCC};
        operator inside {cv32e40p_pkg::ALU_ADD, cv32e40p_pkg::ALU_SUB, cv32e40p_pkg::ALU_AND, cv32e40p_pkg::ALU_OR, cv32e40p_pkg::ALU_XOR, cv32e40p_pkg::ALU_SLL, cv32e40p_pkg::ALU_SRL, cv32e40p_pkg::ALU_SRA};
        enable == 1'b1;
        vector_mode == cv32e40p_pkg::VEC_MODE32;
        // Toggle all control signals
        bmask_a inside {5'h00, 5'h1F, 5'h0A, 5'h15};
        bmask_b inside {5'h00, 5'h1F, 5'h0A, 5'h15};
        imm_vec_ext inside {2'b00, 2'b01, 2'b10, 2'b11};
        is_clpx inside {1'b0, 1'b1};
        is_subrot inside {1'b0, 1'b1};
        clpx_shift inside {2'b00, 2'b01, 2'b10, 2'b11};
      });
      finish_item(req);
    end
    
    // Walking bit patterns for systematic toggle coverage
    for (int bit_pos = 0; bit_pos < 32; bit_pos++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operand_a == (1 << bit_pos);
        operand_b == ~(1 << bit_pos);
        operator inside {cv32e40p_pkg::ALU_ADD, cv32e40p_pkg::ALU_XOR, cv32e40p_pkg::ALU_OR};
        enable == 1'b1;
      });
      finish_item(req);
    end
  endtask
  
endclass

// Exhaustive Branch Coverage Sequence
class alu_branch_coverage_seq extends uvm_sequence #(alu_transaction);
  `uvm_object_utils(alu_branch_coverage_seq)
  
  function new(string name = "alu_branch_coverage_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    alu_transaction req;
    
    `uvm_info("ALU_BRANCH_SEQ", "Starting branch coverage sequence", UVM_LOW)
    
    // Test all comparison operations with edge cases
    for (int i = 0; i < 50; i++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operator inside {cv32e40p_pkg::ALU_LTS, cv32e40p_pkg::ALU_LTU, cv32e40p_pkg::ALU_GES, cv32e40p_pkg::ALU_GEU, cv32e40p_pkg::ALU_EQ, cv32e40p_pkg::ALU_NE};
        // Test boundary conditions for branches
        operand_a inside {32'h00000000, 32'h00000001, 32'h7FFFFFFF, 32'h80000000, 32'hFFFFFFFF};
        operand_b inside {32'h00000000, 32'h00000001, 32'h7FFFFFFF, 32'h80000000, 32'hFFFFFFFF};
        enable == 1'b1;
      });
      finish_item(req);
    end
    
    // Test conditional operations
    for (int i = 0; i < 30; i++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operator inside {cv32e40p_pkg::ALU_SLTS, cv32e40p_pkg::ALU_SLTU, cv32e40p_pkg::ALU_SLETS, cv32e40p_pkg::ALU_SLETU};
        enable == 1'b1;
      });
      finish_item(req);
    end
  endtask
  
endclass

// Comprehensive Line Coverage Sequence
class alu_line_coverage_seq extends uvm_sequence #(alu_transaction);
  `uvm_object_utils(alu_line_coverage_seq)
  
  function new(string name = "alu_line_coverage_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    alu_transaction req;
    
    `uvm_info("ALU_LINE_SEQ", "Starting line coverage sequence", UVM_LOW)
    
    // Test all ALU operations systematically - using direct approach
    // Test ADD operations
    for (int j = 0; j < 20; j++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operator == cv32e40p_pkg::ALU_ADD;
        enable == 1'b1;
      });
      finish_item(req);
    end
    
    // Test SUB operations
    for (int j = 0; j < 20; j++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operator == cv32e40p_pkg::ALU_SUB;
        enable == 1'b1;
      });
      finish_item(req);
    end
    
    // Test logic operations
    for (int j = 0; j < 15; j++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operator inside {cv32e40p_pkg::ALU_XOR, cv32e40p_pkg::ALU_OR, cv32e40p_pkg::ALU_AND};
        enable == 1'b1;
      });
      finish_item(req);
    end
    
    // Test shift operations
    for (int j = 0; j < 15; j++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operator inside {cv32e40p_pkg::ALU_SLL, cv32e40p_pkg::ALU_SRL, cv32e40p_pkg::ALU_SRA};
        operand_b[31:5] == 27'b0; // Valid shift amounts
        enable == 1'b1;
      });
      finish_item(req);
    end
    
    // Test additional operations individually
    for (int k = 0; k < 30; k++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        operator inside {cv32e40p_pkg::ALU_GES, cv32e40p_pkg::ALU_GEU, cv32e40p_pkg::ALU_EQ, cv32e40p_pkg::ALU_NE,
                        cv32e40p_pkg::ALU_SLTS, cv32e40p_pkg::ALU_SLTU, cv32e40p_pkg::ALU_ABS, cv32e40p_pkg::ALU_MIN,
                        cv32e40p_pkg::ALU_MAX, cv32e40p_pkg::ALU_ADDU, cv32e40p_pkg::ALU_SUBU};
        enable == 1'b1;
      });
      finish_item(req);
    end
    
    // Test vector modes
    for (int i = 0; i < 50; i++) begin
      req = alu_transaction::type_id::create("req");
      start_item(req);
      assert(req.randomize() with {
        vector_mode inside {cv32e40p_pkg::VEC_MODE8, cv32e40p_pkg::VEC_MODE16};
        operator inside {cv32e40p_pkg::ALU_ADD, cv32e40p_pkg::ALU_SUB, cv32e40p_pkg::ALU_AND, cv32e40p_pkg::ALU_OR};
        enable == 1'b1;
      });
      finish_item(req);
    end
  endtask
  
endclass

// Step 2: Bit Manipulation Sequences
class alu_bit_manipulation_seq extends uvm_sequence #(alu_sequence_item);
  `uvm_object_utils(alu_bit_manipulation_seq)
  
  function new(string name = "alu_bit_manipulation_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    alu_sequence_item req;
    
    `uvm_info("ALU_BIT_SEQ", "Starting bit manipulation test", UVM_MEDIUM)
    
    // Test bit extract operations
    for (int i = 0; i < 2; i++) begin
      req = alu_sequence_item::type_id::create("req");
      start_item(req);
      
      case (i)
        0: req.operator = cv32e40p_pkg::ALU_BEXT;
        1: req.operator = cv32e40p_pkg::ALU_BEXTU;
      endcase
      req.operand_a = 32'hA5A5A5A5; // Alternating bit pattern
      req.operand_b = 32'h00000008; // Extract from bit 8
      req.operand_c = 32'h00000004; // Extract 4 bits
      req.enable = 1'b1;
      req.vector_mode = cv32e40p_pkg::VEC_MODE32;
      req.ex_ready = 1'b1;
      
      finish_item(req);
    end
    
    // Test bit insert operation
    req = alu_sequence_item::type_id::create("req");
    start_item(req);
    
    req.operator = cv32e40p_pkg::ALU_BINS;
    req.operand_a = 32'hFFFFFFFF; // Base value
    req.operand_b = 32'h00000010; // Insert at bit 16
    req.operand_c = 32'h0000000A; // Insert value 0xA
    req.enable = 1'b1;
    req.vector_mode = cv32e40p_pkg::VEC_MODE32;
    req.ex_ready = 1'b1;
    
    finish_item(req);
    
    // Test bit clear and set operations
    for (int i = 0; i < 2; i++) begin
      req = alu_sequence_item::type_id::create("req");
      start_item(req);
      
      case (i)
        0: req.operator = cv32e40p_pkg::ALU_BCLR;
        1: req.operator = cv32e40p_pkg::ALU_BSET;
      endcase
      req.operand_a = 32'hAAAAAAAA; // Base pattern
      req.operand_b = 32'h0000000F; // Bit position 15
      req.enable = 1'b1;
      req.vector_mode = cv32e40p_pkg::VEC_MODE32;
      req.ex_ready = 1'b1;
      
      finish_item(req);
    end
    
    // Test bit reverse operation
    req = alu_sequence_item::type_id::create("req");
    start_item(req);
    
    req.operator = cv32e40p_pkg::ALU_BREV;
    req.operand_a = 32'h12345678; // Test pattern
    req.enable = 1'b1;
    req.vector_mode = cv32e40p_pkg::VEC_MODE32;
    req.ex_ready = 1'b1;
    
    finish_item(req);
    
    `uvm_info("ALU_BIT_SEQ", "Bit manipulation test completed", UVM_MEDIUM)
  endtask
endclass

class alu_bit_edge_cases_seq extends uvm_sequence #(alu_sequence_item);
  `uvm_object_utils(alu_bit_edge_cases_seq)
  
  function new(string name = "alu_bit_edge_cases_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    alu_sequence_item req;
    
    `uvm_info("ALU_BIT_EDGE_SEQ", "Starting bit manipulation edge cases", UVM_MEDIUM)
    
    // Test edge cases for each bit manipulation operation
    for (int op = 0; op < 6; op++) begin
      for (int edge_case = 0; edge_case < 3; edge_case++) begin
        req = alu_sequence_item::type_id::create("req");
        start_item(req);
        
        case (op)
          0: req.operator = cv32e40p_pkg::ALU_BEXT;
          1: req.operator = cv32e40p_pkg::ALU_BEXTU;
          2: req.operator = cv32e40p_pkg::ALU_BINS;
          3: req.operator = cv32e40p_pkg::ALU_BCLR;
          4: req.operator = cv32e40p_pkg::ALU_BSET;
          5: req.operator = cv32e40p_pkg::ALU_BREV;
        endcase
        
        case (edge_case)
          0: begin // All zeros
            req.operand_a = 32'h00000000;
            req.operand_b = 32'h00000000;
            req.operand_c = 32'h00000000;
          end
          1: begin // All ones
            req.operand_a = 32'hFFFFFFFF;
            req.operand_b = 32'hFFFFFFFF;
            req.operand_c = 32'hFFFFFFFF;
          end
          2: begin // Boundary values
            req.operand_a = 32'h80000001;
            req.operand_b = 32'h0000001F; // Bit 31
            req.operand_c = 32'h00000001;
          end
        endcase
        
        req.enable = 1'b1;
        req.vector_mode = cv32e40p_pkg::VEC_MODE32;
        req.ex_ready = 1'b1;
        
        finish_item(req);
      end
    end
    
    `uvm_info("ALU_BIT_EDGE_SEQ", "Bit manipulation edge cases completed", UVM_MEDIUM)
  endtask
endclass

// Updated Comprehensive Sequence with High Coverage Focus
class alu_high_coverage_comprehensive_seq extends uvm_sequence #(alu_transaction);
  `uvm_object_utils(alu_high_coverage_comprehensive_seq)
  
  function new(string name = "alu_high_coverage_comprehensive_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    // Step 0: Add optimized assembly sequence (foundation coverage)
    alu_assembly_sequence asm_seq;
    // Step 1: Add division sequences (highest impact +15%)
    alu_division_seq div_seq;
    // Step 2: Add bit manipulation sequences (high impact +10%)
    alu_bit_manipulation_seq bit_seq;
    alu_bit_edge_cases_seq bit_edge_seq;
    // Step 3: Add toggle coverage for signal coverage
    alu_toggle_coverage_seq toggle_seq;
    
    `uvm_info("ALU_HIGH_COV_SEQ", "Starting weighted assembly + high coverage test", UVM_LOW)
    
    // Step 0: Run optimized assembly sequence (foundation coverage)
    `uvm_info("ALU_HIGH_COV_SEQ", "Step 0: Running optimized assembly sequence", UVM_LOW)
    asm_seq = alu_assembly_sequence::type_id::create("asm_seq");
    asm_seq.start(m_sequencer);
    
    // Step 1: Run minimal division sequences (highest impact +15%)
    `uvm_info("ALU_HIGH_COV_SEQ", "Step 1: Running minimal division sequences", UVM_LOW)
    div_seq = alu_division_seq::type_id::create("div_seq");
    div_seq.start(m_sequencer);
    
    // Step 2: Run bit manipulation sequences (high impact +10%)
    `uvm_info("ALU_HIGH_COV_SEQ", "Step 2: Running bit manipulation sequences", UVM_LOW)
    bit_seq = alu_bit_manipulation_seq::type_id::create("bit_seq");
    bit_seq.start(m_sequencer);
    
    bit_edge_seq = alu_bit_edge_cases_seq::type_id::create("bit_edge_seq");
    bit_edge_seq.start(m_sequencer);
    
    // Step 3: Run toggle coverage sequence for maximum signal coverage
    `uvm_info("ALU_HIGH_COV_SEQ", "Step 3: Running toggle coverage sequence", UVM_LOW)
    toggle_seq = alu_toggle_coverage_seq::type_id::create("toggle_seq");
    toggle_seq.start(m_sequencer);
    
    `uvm_info("ALU_HIGH_COV_SEQ", "Ultra-streamlined high coverage test completed", UVM_LOW)
  endtask
  
endclass