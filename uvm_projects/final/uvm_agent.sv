// Copyright 2024 ChipAgents
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// UVM Agent for CV32E40P ALU                                                //
//                                                                            //
// Description: Complete UVM agent containing driver, monitor, and sequencer //
//              for the CV32E40P ALU verification                             //
////////////////////////////////////////////////////////////////////////////////

`include "uvm_macros.svh"

import uvm_pkg::*;
import cv32e40p_alu_pkg::*;

// ALU Sequencer
class alu_sequencer extends uvm_sequencer #(alu_transaction);
  `uvm_component_utils(alu_sequencer)
  
  function new(string name = "alu_sequencer", uvm_component parent);
    super.new(name, parent);
  endfunction
  
endclass

// ALU Agent
class alu_agent extends uvm_agent;
  `uvm_component_utils(alu_agent)
  
  alu_driver    driver;
  alu_monitor   monitor;
  alu_sequencer sequencer;
  
  function new(string name = "alu_agent", uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    driver = alu_driver::type_id::create("driver", this);
    monitor = alu_monitor::type_id::create("monitor", this);
    sequencer = alu_sequencer::type_id::create("sequencer", this);
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    driver.seq_item_port.connect(sequencer.seq_item_export);
  endfunction
  
endclass