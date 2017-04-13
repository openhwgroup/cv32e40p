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
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
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

  // irq_req for controller
  output logic        irq_req_ctrl_o,
  output logic        irq_sec_ctrl_o,
  output logic  [4:0] irq_id_ctrl_o,

  // handshake signals to controller
  input  logic        ctrl_ack_i,
  input  logic        ctrl_done_i,

  output logic        trap_o,

  // external interrupt lines
  input  logic        irq_i,          // level-triggered interrupt inputs
  input  logic        irq_sec_i,      // interrupt secure bit from EU
  input  logic  [4:0] irq_id_i,       // interrupt id [0,1,....31]

  input  logic        m_IE_i,         // interrupt enable bit from CSR (M mode)
  input  logic        u_IE_i,         // interrupt enable bit from CSR (U mode)
  input  PrivLvl_t    current_priv_lvl_i,

  // from debug unit
  input  logic [DBG_SETS_W-1:0] dbg_settings_i
);


  enum logic [1:0] { IDLE, IRQ_PENDING, IRQ_ACK} exc_ctrl_cs, exc_ctrl_ns;

  logic irq_enable_ext, irq_enable_int;
  logic [4:0] irq_id_q;
  logic trap_int;
  logic store_irq_id;
  logic irq_q, irq_sec_q;

  // a trap towards the debug unit is generated when one of the
  // following conditions are true:
  // - ebreak instruction encountered
  // - single-stepping mode enabled
  // - illegal instruction exception and IIE bit is set
  // - IRQ and INTE bit is set and no exception is currently running
  // - Debuger requests halt
/*
  assign trap_int =    (dbg_settings_i[DBG_SETS_SSTE])
                      | (ecall_insn_i            & dbg_settings_i[DBG_SETS_ECALL])
                      | (ebrk_insn_i             & dbg_settings_i[DBG_SETS_EBRK])
                      | (illegal_insn_i          & dbg_settings_i[DBG_SETS_EILL])
                      | (irq_enable_int & irq_i  & dbg_settings_i[DBG_SETS_IRQ]);
*/
  assign trap_o = 1'b0;

  assign irq_enable_int =  ((u_IE_i | irq_sec_q) & current_priv_lvl_i == PRIV_LVL_U) | (m_IE_i & current_priv_lvl_i == PRIV_LVL_M);
  assign irq_enable_ext =  ((u_IE_i | irq_sec_i) & current_priv_lvl_i == PRIV_LVL_U) | (m_IE_i & current_priv_lvl_i == PRIV_LVL_M);


  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      irq_id_q    <= '0;
      irq_q       <= 1'b0;
      irq_sec_q   <= 1'b0;
      exc_ctrl_cs <= IDLE;
    end else begin
      if (store_irq_id) begin
        irq_id_q  <= irq_id_i;
      end
      irq_q       <= irq_i;
      irq_sec_q   <= irq_sec_i;
      exc_ctrl_cs <= exc_ctrl_ns;
    end
  end

  // Exception controller FSM
  always_comb
  begin

    exc_ctrl_ns     = exc_ctrl_cs;

    irq_req_ctrl_o  = 1'b0;
    irq_id_ctrl_o   = irq_id_q;
    irq_sec_ctrl_o  = irq_sec_q;

    store_irq_id    = 1'b0;

/*
    trap_addr_mux_o = TRAP_MACHINE;
    pc_mux_o        = EXC_PC_IRQ;
*/

    unique case (exc_ctrl_cs)

      IDLE:
      begin

        //trap_o        = dbg_settings_i[DBG_SETS_SSTE];
        if(irq_enable_ext & irq_i)
          exc_ctrl_ns = IRQ_PENDING;
/*
       end else
       begin

          irq_req_o   = 1'b0;

          unique case(1'b1)
            exc_req_int & ctr_decoding_i: begin
              exc_ctrl_ns = ctrl_ack_i ? WAIT_CONTROLLER_EXC : IDLE;
              exc_req_o   = 1'b1;
            end
            ecall_insn_i & ctr_decoding_i:
              exc_ctrl_ns = ctrl_ack_i ? WAIT_CONTROLLER_ECALL : IDLE;
            ebrk_insn_i & ctr_decoding_i:
              exc_ctrl_ns = ctrl_ack_i ? WAIT_CONTROLLER_DBG : IDLE;
            default:;
          endcase
        end
*/
      end

      IRQ_PENDING:
      begin
        //current_priv_lvl_i could not change
        //only previous interrupts, ecall or xret can change that:
          //if an ecall is the EX_STAGE, the exc_controller would be in WAIT_CONTROLLER_ECALL
          //if an exception is raised, the exc_controller would be in WAIT_CONTROLLER_EXC
          //if an xret is the EX_STAGE, the exc_controller would be in IDLE, therefore the interrupt would be served once the controller goes back to DECODE

        if(irq_enable_int & irq_q) begin
            //here we check again because the previous cycle could have modified the int enable
            //meanwhile another instruction can modify irq_enable therefore the controller is giving the ctrl_ack_i at least next cycle after the request in normal cases
            //this means that the next cycle, irq_enable is zero an we are in the else statement
            irq_req_ctrl_o  = 1'b1;
            exc_ctrl_ns     = ctrl_ack_i ? IRQ_ACK : IRQ_PENDING;
            store_irq_id    = ctrl_ack_i;
        end else begin
            exc_ctrl_ns     = ctrl_ack_i ?    IDLE : IRQ_PENDING;
        end

/*
            unique case(current_priv_lvl_i)
              PRIV_LVL_U:
                exc_ctrl_ns = irq_sec_q ? WAIT_CONTROLLER_IRQ_M : WAIT_CONTROLLER_IRQ_U;
              PRIV_LVL_M:
                exc_ctrl_ns = WAIT_CONTROLLER_IRQ_M;
              default:;
            endcase
        end else begin
           //an operation in the pipeline changed the irq_enable, therefore we do not tell the controller anything
           //about interrupts and we go back to IDLE. The controller will go back in DECODE in case it was in the WAIT_IRQ_FLUSH_EX stage
           exc_ctrl_ns = IDLE;
        end
*/
      end

      IRQ_ACK:
      begin
        exc_ctrl_ns = ctrl_done_i ?    IDLE : IRQ_ACK;
      end

/*
      WAIT_CONTROLLER_EXC:
      begin

        exc_int_req_o   = 1'b1;

        trap_o          = trap_int;
        cause_o         = EXC_CAUSE_ILLEGAL_INSN;
        pc_mux_o        = EXC_PC_ILLINSN;
        if (ctrl_done_i) begin
          exc_ctrl_ns  = IDLE;
        end
      end

      WAIT_CONTROLLER_IRQ_U:
      begin
        irq_n           = 1'b0;
        irq_sec_n       = 1'b0;

        trap_o          = trap_int;
        cause_o         = cause_int_q;
        pc_mux_o        = EXC_PC_IRQ;
        trap_addr_mux_o = TRAP_USER;

        if (ctrl_done_i) begin
          exc_ctrl_ns  = IDLE;
        end
      end

      WAIT_CONTROLLER_IRQ_M:
      begin
        irq_n           = 1'b0;
        irq_sec_n       = 1'b0;

        trap_o          = trap_int;
        cause_o         = cause_int_q;
        pc_mux_o        = EXC_PC_IRQ;
        trap_addr_mux_o = TRAP_MACHINE;
        if (ctrl_done_i) begin
          exc_ctrl_ns  = IDLE;
        end
      end

      WAIT_CONTROLLER_DBG:
      begin
        exc_ctrl_ns  = IDLE;
        cause_o      = EXC_CAUSE_BREAKPOINT;
        trap_o       = trap_int;
        if (ctrl_done_i) begin
          exc_ctrl_ns  = IDLE;
        end
      end

      WAIT_CONTROLLER_ECALL:
      begin
        trap_o       = trap_int;
        pc_mux_o     = EXC_PC_ECALL;
        unique case(current_priv_lvl_i)
          PRIV_LVL_U: begin
            cause_o         = EXC_CAUSE_ECALL_UMODE;
            trap_addr_mux_o = TRAP_MACHINE;
          end
          PRIV_LVL_M: begin
            cause_o         = EXC_CAUSE_ECALL_MMODE;
            trap_addr_mux_o = TRAP_MACHINE;
          end
        endcase
        if (ctrl_done_i) begin
          exc_ctrl_ns  = IDLE;
        end
      end
*/

      default:
      begin
        exc_ctrl_ns = IDLE;
      end
    endcase
  end



`ifndef SYNTHESIS
  // synopsys translate_off
  // evaluate at falling edge to avoid duplicates during glitches
  always_ff @(negedge clk)
  begin
    if (rst_n && ctrl_done_i)
      $display("%t: Entering exception routine. [%m]", $time);
  end
  // synopsys translate_on
`endif

endmodule
