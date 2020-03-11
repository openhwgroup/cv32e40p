// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                                                                          //
// Author:                              Francesco Minervini - minervif@student.ethz.ch                      //
//                                                                                                          //
// Additional contributions by:         Davide Schiavone - pschiavo@iis.ee.ethz.ch                          //
//                                      Andrea Bettati - andrea.bettati@studenti.unipr.it                   //
// Design Name:                         Interrupt generator                                                 //
// Project Name:                        RI5CY, Zeroriscy                                                    //
// Language:                            SystemVerilog                                                       //
//                                                                                                          //
// Description:                         Send interrupt request to core choosing one option between:         //
//                                      - Random;                                                           //
//                                      - Standard;                                                         //
//                                      - PC value-triggering                                               //
//                                                                                                          //
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
import riscv_defines::*;
import perturbation_defines::*;
`include "riscv_config.sv"

module riscv_random_interrupt_generator
(
    input logic                        rst_ni,
    input logic                        clk_i,
    input logic                        irq_i,
    input logic                        irq_ack_i,
    output logic [IRQ_LINES_NUM-1:0]   irq_rnd_lines_o,
    output logic                       irq_ack_o,
    input logic  [31:0]                irq_mode_i,
    input logic  [31:0]                irq_min_cycles_i,
    input logic  [31:0]                irq_max_cycles_i,
    input logic  [31:0]                irq_min_id_i,
    input logic  [31:0]                irq_max_id_i,
    output logic [31:0]                irq_act_id_o,
    output logic                       irq_id_we_o,
    input logic  [31:0]                irq_pc_id_i,
    input logic  [31:0]                irq_pc_trig_i,
    // software defined mode i/o
    input logic  [63:0]                irq_lines_i
);

`ifndef VERILATOR
class rand_irq_cycles;
    rand int n;
endclass : rand_irq_cycles

class rand_irq_id;
    rand int n;
    rand bit [63:0] rand_word;
endclass : rand_irq_id

logic [31:0] irq_mode_q;
logic        irq_random;
logic [5:0]  irq_id_random;
logic        irq_ack_random;
logic        irq_monitor;
logic [5:0]  irq_id_monitor;
logic        irq_ack_monitor;

logic        irq_sd;
logic [63:0] irq_lines;
logic        ack_flag;
logic        irq_lines_changed;


// struct irq_lines
typedef struct packed {
  logic        irq_software;
  logic        irq_timer;
  logic        irq_external;
  logic [14:0] irq_fast;
  logic        irq_nmi;
  logic [31:0] irq_fastx;
} Interrupts_tb_t;

Interrupts_tb_t irq_lines_q, irq_lines_n;
Interrupts_tb_t irq_rnd_lines, irq_pc_trig_lines,irq_sd_lines;


assign irq_ack_o       = irq_ack_i;
assign irq_rnd_lines_o = irq_lines_q;

always_ff @(posedge clk_i or negedge rst_ni)
begin
    if(~rst_ni) begin
        irq_mode_q  <= 0;
        irq_lines_q <= '0;
    end else begin
        irq_mode_q  <= irq_mode_i;
        irq_lines_q <= irq_lines_n;
    end
end

always_comb
begin
  unique case (irq_mode_q)
    RANDOM:
    begin
      // UPDATE LOGIC:
      // random irq word id stored and updated every time
      // an interrupt is taken by the core

      irq_lines_n = irq_rnd_lines;
    end

    PC_TRIG:
    begin
      // TODO generate individual irq lines
      irq_lines_n = irq_pc_trig_lines;
    end

    SOFTWARE_DEFINED:
    begin
      // UPDATE LOGIC:
      irq_lines_n = irq_sd_lines;
    end

    default:
    begin
      irq_lines_n = '0;
    end
  endcase
end

// RANDOM INTERRUPTS PROCESS
// Generates a random word irq_rnd_lines [18:0] at a random time.
// The generated word is stored in irq_lines_q.

initial
begin
  automatic rand_irq_cycles wait_cycles = new();
  automatic rand_irq_id value = new();
  int temp,i, min_irq_cycles, max_irq_cycles, min_irq_id, max_irq_id;
  irq_random     = 1'b0;
  irq_rnd_lines  = '0;
  while(1) begin
    @(posedge clk_i);

    wait(irq_mode_q == RANDOM);
    min_irq_id  = irq_min_id_i;
    max_irq_id  = irq_max_id_i;
    min_irq_cycles = irq_min_cycles_i;
    max_irq_cycles = irq_max_cycles_i;

    // generate random word and mask it with lower/upper bounds
    temp = value.randomize();
    for(int i = min_irq_id-1; i >= 0; i--) begin
      value.rand_word[i] = 0;
    end

    for(int i = max_irq_id+1; i <= 63; i++) begin
      value.rand_word[i] = 0;
    end

    temp = wait_cycles.randomize() with{
        n >= min_irq_cycles;
        n <= max_irq_cycles;
    };

    irq_random    = 1'b1;
    irq_act_id_o  = value.n;
    @(posedge clk_i);
    irq_random    = 1'b0;

    // random irq word: update logic
    while (wait_cycles.n) begin
      @(posedge clk_i)
      irq_lines <= irq_lines_i;
      wait_cycles.n--;
    end

    // map random irq word to physical lines
    irq_rnd_lines.irq_software = value.rand_word [3];
    irq_rnd_lines.irq_timer    = value.rand_word [7];
    irq_rnd_lines.irq_external = value.rand_word [11];
    irq_rnd_lines.irq_fast     = value.rand_word [30:16];
    irq_rnd_lines.irq_nmi      = value.rand_word [31];
    irq_rnd_lines.irq_fastx    = value.rand_word [63:32];

    //clear interrupt request
    wait(irq_mode_q == STANDARD);
    irq_rnd_lines  = '0;

  end
end

// check if signal changed @posedge
assign irq_lines_changed = (irq_lines != irq_lines_i) ? 1 : 0;


// SOFTWARE DEFINED INTERRUPTS PROCESS
// Samples irq lines (word) as defined by software

initial
begin
  irq_sd_lines = 32'b0;
  while(1) begin
    irq_sd       = 1'b0;
    ack_flag     = 1'b0;

    wait (irq_mode_q == SOFTWARE_DEFINED);

    // blocking wait for a valid sd_id
    while(irq_lines_i != 0) begin
      @(posedge clk_i);
        // sample input lines
        irq_sd_lines.irq_software = irq_lines_i [3];
        irq_sd_lines.irq_timer    = irq_lines_i [7];
        irq_sd_lines.irq_external = irq_lines_i [11];
        irq_sd_lines.irq_fast     = irq_lines_i [30:16];
        irq_sd_lines.irq_nmi      = irq_lines_i [31];
        irq_sd_lines.irq_fastx    = irq_lines_i [63:32];
        irq_sd    = 1'b1;
    end

    @(posedge clk_i);

  end
end

//PC Trig Process
initial
begin
  int pc_value;
  irq_monitor    = 1'b0;
  pc_value = 0;
  irq_pc_trig_lines = '0;
  wait(irq_mode_q == PC_TRIG);
  wait(irq_pc_id_i == irq_pc_trig_i);
  irq_monitor = 1'b1;

  // build irq monitor word
  irq_pc_trig_lines.irq_software = 1'b1;

  // irq monitor word: update logic
  while(~irq_lines_changed) begin
    @(posedge clk_i);
    irq_lines <= irq_lines_i;
  end

  irq_pc_trig_lines.irq_software = irq_lines_i [3];
  irq_pc_trig_lines.irq_timer    = irq_lines_i [7];
  irq_pc_trig_lines.irq_external = irq_lines_i [11];
  irq_pc_trig_lines.irq_fast     = irq_lines_i [30:16];
  irq_pc_trig_lines.irq_nmi      = irq_lines_i [31];

  irq_monitor    = 1'b0;
  irq_id_monitor = '0;
end

initial
begin
    while(1) begin
        irq_id_we_o = 1'b0;
        wait(irq_ack_i == 1'b1);
        irq_id_we_o = 1'b1;   //Give the write enable to store the core response
        @(posedge clk_i);
    end
end

`endif
endmodule
