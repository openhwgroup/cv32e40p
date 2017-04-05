// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Design Name:    Exception Controller                                       //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Exception Controller of the pipelined processor            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import riscv_defines::*;

module riscv_exc_controller
#(
  parameter PULP_SECURE = 0
)
(
  input  logic        clk,
  input  logic        rst_n,

  // handshake signals to controller
  output logic        int_req_o,
  output logic        ext_req_o,
  input  logic        ack_i,

  input  logic        ctr_decoding_i,
  output logic        trap_o,

  // to IF stage
  output logic  [1:0] pc_mux_o,       // selects target PC for exception

  // interrupt lines
  input  logic        irq_i,          // level-triggered interrupt inputs
  input  logic  [4:0] irq_id_i,       // interrupt id [0,1,....31]
  input  logic        irq_enable_i,   // interrupt enable bit from CSR

  // from decoder
  input  logic        ebrk_insn_i,    // ebrk instruction encountered (EBREAK)
  input  logic        illegal_insn_i, // illegal instruction encountered
  input  logic        ecall_insn_i,   // ecall instruction encountered

  // from/to CSR
  input  PrivLvl_t    current_priv_lvl_i,
  output logic [5:0]  cause_o,
  output logic        save_cause_o,

  // from debug unit
  input  logic [DBG_SETS_W-1:0] dbg_settings_i
);


  enum logic [1:0] { IDLE, WAIT_CONTROLLER_INT, WAIT_CONTROLLER_EXT, WAIT_CONTROLLER_DBG } exc_ctrl_cs, exc_ctrl_ns;

  logic int_req_int, ext_req_int, ext_req_n;
  logic [1:0] pc_mux_int, pc_mux_int_q;
  logic [5:0] cause_int, cause_int_q;
  logic trap_int;

  // a trap towards the debug unit is generated when one of the
  // following conditions are true:
  // - ebreak instruction encountered
  // - single-stepping mode enabled
  // - illegal instruction exception and IIE bit is set
  // - IRQ and INTE bit is set and no exception is currently running
  // - Debuger requests halt
  assign trap_int =    (dbg_settings_i[DBG_SETS_SSTE])
                      | (ecall_insn_i            & dbg_settings_i[DBG_SETS_ECALL])
                      | (ebrk_insn_i             & dbg_settings_i[DBG_SETS_EBRK])
                      | (illegal_insn_i          & dbg_settings_i[DBG_SETS_EILL])
                      | (irq_enable_i & irq_i    & dbg_settings_i[DBG_SETS_IRQ]);

// request for exception -> only from the ID stage
assign int_req_int = ecall_insn_i
                     | illegal_insn_i;

assign ext_req_int = irq_enable_i & irq_i;


  // Exception cause and ISR address selection
  always_comb
  begin
    cause_int  = 6'b0;
    pc_mux_int = '0;

    if (irq_enable_i & irq_i) begin
      // pc_mux_int is a critical signal, so try to get it as soon as possible
      pc_mux_int = EXC_PC_IRQ;
      cause_int = {1'b1,irq_id_i};
    end
    else begin
      //interrupts have priority over exceptions
      unique case(1'b1)
        ebrk_insn_i: begin
          cause_int  = EXC_CAUSE_BREAKPOINT;
        end
        ecall_insn_i: begin
          unique case(current_priv_lvl_i)
            PRIV_LVL_U: cause_int  = EXC_CAUSE_ECALL_UMODE;
            PRIV_LVL_M: cause_int  = EXC_CAUSE_ECALL_MMODE;
          endcase
          pc_mux_int = EXC_PC_ECALL;
        end
        illegal_insn_i: begin
          cause_int  = EXC_CAUSE_ILLEGAL_INSN;
          pc_mux_int = EXC_PC_ILLINSN;
        end
        default:;
      endcase
    end
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      cause_int_q  <= '0;
      pc_mux_int_q <= '0;
      ext_req_o    <= 1'b0;
    end else begin
      if (exc_ctrl_cs == IDLE && (ctr_decoding_i | ext_req_int)) begin
        // save cause and ISR when new irq request is first sent to controller
        cause_int_q  <= cause_int;
        pc_mux_int_q <= pc_mux_int;
      end
      ext_req_o <= ext_req_n; //interrupts broken path
    end
  end


  // Exception cause and mux output (with bypass)
  assign cause_o      = cause_int_q;
  assign pc_mux_o     = pc_mux_int_q;

  // Exception controller FSM
  always_comb
  begin
    exc_ctrl_ns  = exc_ctrl_cs;
    int_req_o    = 1'b0;
    ext_req_n    = 1'b0;
    save_cause_o = 1'b0;
    trap_o       = 1'b0;

    unique case (exc_ctrl_cs)

      IDLE:
      begin
        int_req_o = int_req_int;
        trap_o    = dbg_settings_i[DBG_SETS_SSTE];

        if(ext_req_int) begin
           exc_ctrl_ns = WAIT_CONTROLLER_EXT;
           ext_req_n   = 1'b1;
        end else begin
          unique case(1'b1)
            int_req_int & ctr_decoding_i:
              exc_ctrl_ns = WAIT_CONTROLLER_INT;
            ebrk_insn_i & ctr_decoding_i:
              exc_ctrl_ns = WAIT_CONTROLLER_DBG;
            default:;
          endcase
        end
      end

      WAIT_CONTROLLER_INT:
      begin
        int_req_o = 1'b1;
        trap_o    = trap_int;
        if (ack_i) begin
          save_cause_o = 1'b1;
          exc_ctrl_ns  = IDLE;
        end
      end

      WAIT_CONTROLLER_EXT:
      begin
        ext_req_n = 1'b1;
        trap_o    = trap_int;
        if (ack_i) begin
          save_cause_o = 1'b1;
          exc_ctrl_ns  = IDLE;
        end
      end

      WAIT_CONTROLLER_DBG:
      begin
        exc_ctrl_ns  = IDLE;
        trap_o       = trap_int;
        if (ack_i) begin
          exc_ctrl_ns  = IDLE;
        end
      end

      default:
      begin
        exc_ctrl_ns = IDLE;
      end
    endcase
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
      exc_ctrl_cs <= IDLE;
    else
      exc_ctrl_cs <= exc_ctrl_ns;
  end


`ifndef SYNTHESIS
  // synopsys translate_off
  // evaluate at falling edge to avoid duplicates during glitches
  always_ff @(negedge clk)
  begin
    if (rst_n && (int_req_o | ext_req_o) && ack_i)
      $display("%t: Entering exception routine. [%m]", $time);
  end
  // synopsys translate_on
`endif

endmodule
