// Copyright 2024 ChipAgents
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// UVM Driver for CV32E40P ALU                                               //
//                                                                            //
// Description: UVM driver that drives stimulus to the ALU DUT through       //
//              the virtual interface                                         //
////////////////////////////////////////////////////////////////////////////////

`include "uvm_macros.svh"

import uvm_pkg::*;
import cv32e40p_alu_pkg::*;

// ALU Driver
class alu_driver extends uvm_driver #(alu_transaction);
  `uvm_component_utils(alu_driver)
  
  virtual alu_interface vif;
  
  function new(string name = "alu_driver", uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual alu_interface)::get(this, "", "vif", vif))
      `uvm_fatal("DRIVER", "Could not get virtual interface")
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    alu_transaction req;
    
    forever begin
      seq_item_port.get_next_item(req);
      drive_transaction(req);
      seq_item_port.item_done();
    end
  endtask
  
  virtual task drive_transaction(alu_transaction req);
    @(posedge vif.clk);
    vif.enable_i      <= req.enable;
    vif.operator_i    <= req.operator;
    vif.operand_a_i   <= req.operand_a;
    vif.operand_b_i   <= req.operand_b;
    vif.operand_c_i   <= req.operand_c;
    vif.vector_mode_i <= req.vector_mode;
    vif.bmask_a_i     <= req.bmask_a;
    vif.bmask_b_i     <= req.bmask_b;
    vif.imm_vec_ext_i <= req.imm_vec_ext;
    vif.is_clpx_i     <= req.is_clpx;
    vif.is_subrot_i   <= req.is_subrot;
    vif.clpx_shift_i  <= req.clpx_shift;
    vif.ex_ready_i    <= req.ex_ready;
    
    // Wait for operation to complete
    @(posedge vif.clk);
    while (!vif.ready_o && vif.enable_i) begin
      @(posedge vif.clk);
    end
  endtask
  
endclass