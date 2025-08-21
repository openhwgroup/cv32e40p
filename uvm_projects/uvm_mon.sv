// Copyright 2024 ChipAgents
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// UVM Monitor for CV32E40P ALU                                              //
//                                                                            //
// Description: UVM monitor that observes ALU transactions and sends them    //
//              to the scoreboard for checking                               //
////////////////////////////////////////////////////////////////////////////////

`include "uvm_macros.svh"

import uvm_pkg::*;
import cv32e40p_alu_pkg::*;

// ALU Monitor
class alu_monitor extends uvm_monitor;
  `uvm_component_utils(alu_monitor)
  
  virtual alu_interface vif;
  uvm_analysis_port #(alu_transaction) ap;
  
  function new(string name = "alu_monitor", uvm_component parent);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual alu_interface)::get(this, "", "vif", vif))
      `uvm_fatal("MONITOR", "Could not get virtual interface")
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    alu_transaction trans;
    
    forever begin
      @(posedge vif.clk);
      if (vif.enable_i) begin
        trans = alu_transaction::type_id::create("trans");
        
        // Capture inputs
        trans.enable = vif.enable_i;
        trans.operator = vif.operator_i;
        trans.operand_a = vif.operand_a_i;
        trans.operand_b = vif.operand_b_i;
        trans.operand_c = vif.operand_c_i;
        trans.vector_mode = vif.vector_mode_i;
        trans.bmask_a = vif.bmask_a_i;
        trans.bmask_b = vif.bmask_b_i;
        trans.imm_vec_ext = vif.imm_vec_ext_i;
        trans.is_clpx = vif.is_clpx_i;
        trans.is_subrot = vif.is_subrot_i;
        trans.clpx_shift = vif.clpx_shift_i;
        trans.ex_ready = vif.ex_ready_i;
        
        // Wait for outputs to be valid
        wait(vif.ready_o);
        
        // Capture outputs
        trans.result = vif.result_o;
        trans.comparison_result = vif.comparison_result_o;
        trans.ready = vif.ready_o;
        
        ap.write(trans);
      end
    end
  endtask
  
endclass