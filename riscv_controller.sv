// Copyright 2017 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Main controller                                            //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Main CPU controller of the processor                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import riscv_defines::*;

module riscv_controller
#(
  parameter FPU               = 0
)
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        fetch_enable_i,             // Start the decoding
  output logic        ctrl_busy_o,                // Core is busy processing instructions
  output logic        first_fetch_o,              // Core is at the FIRST FETCH stage
  output logic        is_decoding_o,              // Core is in decoding state

  // decoder related signals
  output logic        deassert_we_o,              // deassert write enable for next instruction

  input  logic        illegal_insn_i,             // decoder encountered an invalid instruction
  input  logic        ecall_insn_i,               // ecall encountered an mret instruction
  input  logic        mret_insn_i,                // decoder encountered an mret instruction
  input  logic        uret_insn_i,                // decoder encountered an uret instruction
  input  logic        pipe_flush_i,               // decoder wants to do a pipe flush
  input  logic        ebrk_insn_i,                // decoder encountered an ebreak instruction
  input  logic        csr_status_i,               // decoder encountered an csr status instruction
  input  logic        instr_multicycle_i,         // true when multiple cycles are decoded

  // from IF/ID pipeline
  input  logic        instr_valid_i,              // instruction coming from IF/ID pipeline is valid

  // from prefetcher
  output logic        instr_req_o,                // Start fetching instructions

  // to prefetcher
  output logic        pc_set_o,                   // jump to address set by pc_mux
  output logic [2:0]  pc_mux_o,                   // Selector in the Fetch stage to select the rigth PC (normal, jump ...)
  output logic [1:0]  exc_pc_mux_o,               // Selects target PC for exception
  output logic        trap_addr_mux_o,            // Selects trap address base

  // LSU
  input  logic        data_req_ex_i,              // data memory access is currently performed in EX stage
  input  logic        data_misaligned_i,
  input  logic        data_load_event_i,

  // from ALU
  input  logic        mult_multicycle_i,          // multiplier is taken multiple cycles and uses op c as storage

  // APU dependency checks
  input  logic        apu_en_i,
  input  logic        apu_read_dep_i,
  input  logic        apu_write_dep_i,

  output logic        apu_stall_o,

  // jump/branch signals
  input  logic        branch_taken_ex_i,          // branch taken signal from EX ALU
  input  logic [1:0]  jump_in_id_i,               // jump is being calculated in ALU
  input  logic [1:0]  jump_in_dec_i,              // jump is being calculated in ALU

  // Interrupt Controller Signals
  input  logic        irq_req_ctrl_i,
  input  logic        irq_sec_ctrl_i,
  input  logic [4:0]  irq_id_ctrl_i,
  input  logic        m_IE_i,                     // interrupt enable bit from CSR (M mode)
  input  logic        u_IE_i,                     // interrupt enable bit from CSR (U mode)
  input  PrivLvl_t    current_priv_lvl_i,

  output logic        irq_ack_o,
  output logic [4:0]  irq_id_o,

  output logic [5:0]  exc_cause_o,
  output logic        exc_ack_o,
  output logic        exc_kill_o,

  output logic        csr_save_if_o,
  output logic        csr_save_id_o,
  output logic [5:0]  csr_cause_o,
  output logic        csr_irq_sec_o,
  output logic        csr_restore_mret_id_o,
  output logic        csr_restore_uret_id_o,
  output logic        csr_save_cause_o,

  // Debug Signals
  input  logic        dbg_req_i,                  // a trap was hit, so we have to flush EX and WB
  output logic        dbg_ack_o,                  // we stopped and give control to debug now

  input  logic        dbg_stall_i,                // Pipeline stall is requested
  input  logic        dbg_jump_req_i,             // Change PC to value from debug unit

  input  logic [DBG_SETS_W-1:0] dbg_settings_i,
  output logic        dbg_trap_o,

  // Regfile target
  input  logic [5:0]  regfile_alu_waddr_id_i,     // currently decoded target address

  // Forwarding signals from regfile
  input  logic        regfile_we_ex_i,            // FW: write enable from  EX stage
  input  logic [5:0]  regfile_waddr_ex_i,         // FW: write address from EX stage
  input  logic        regfile_we_wb_i,            // FW: write enable from  WB stage
  input  logic        regfile_alu_we_fw_i,        // FW: ALU/MUL write enable from  EX stage

  // forwarding signals
  output logic [1:0]  operand_a_fw_mux_sel_o,     // regfile ra data selector form ID stage
  output logic [1:0]  operand_b_fw_mux_sel_o,     // regfile rb data selector form ID stage
  output logic [1:0]  operand_c_fw_mux_sel_o,     // regfile rc data selector form ID stage

  // forwarding detection signals
  input logic         reg_d_ex_is_reg_a_i,
  input logic         reg_d_ex_is_reg_b_i,
  input logic         reg_d_ex_is_reg_c_i,
  input logic         reg_d_wb_is_reg_a_i,
  input logic         reg_d_wb_is_reg_b_i,
  input logic         reg_d_wb_is_reg_c_i,
  input logic         reg_d_alu_is_reg_a_i,
  input logic         reg_d_alu_is_reg_b_i,
  input logic         reg_d_alu_is_reg_c_i,

  // stall signals
  output logic        halt_if_o,
  output logic        halt_id_o,

  output logic        misaligned_stall_o,
  output logic        jr_stall_o,
  output logic        load_stall_o,

  input  logic        id_ready_i,                 // ID stage is ready

  input  logic        ex_valid_i,                 // EX stage is done

  input  logic        wb_ready_i,                 // WB stage is ready

  // Performance Counters
  output logic        perf_jump_o,                // we are executing a jump instruction   (j, jr, jal, jalr)
  output logic        perf_jr_stall_o,            // stall due to jump-register-hazard
  output logic        perf_ld_stall_o             // stall due to load-use-hazard
);

  // FSM state encoding
  enum  logic [4:0] { RESET, BOOT_SET, SLEEP, WAIT_SLEEP, FIRST_FETCH,
                      DECODE,
                      IRQ_TAKEN_ID, IRQ_TAKEN_IF, IRQ_FLUSH, ELW_EXE,
                      FLUSH_EX, FLUSH_WB,
                      DBG_SIGNAL, DBG_SIGNAL_SLEEP, DBG_SIGNAL_ELW,
                      DBG_WAIT, DBG_WAIT_BRANCH, DBG_WAIT_SLEEP, DBG_WAIT_ELW } ctrl_fsm_cs, ctrl_fsm_ns;

  logic jump_done, jump_done_q, jump_in_dec, branch_in_id;
  logic boot_done, boot_done_q;
  logic irq_enable_int;

`ifndef SYNTHESIS
  // synopsys translate_off
  // make sure we are called later so that we do not generate messages for
  // glitches
  always_ff @(negedge clk)
  begin
    // print warning in case of decoding errors
    if (is_decoding_o && illegal_insn_i) begin
      $display("%t: Illegal instruction (core %0d) at PC 0x%h:", $time, riscv_core.core_id_i,
               riscv_id_stage.pc_id_i);
    end
  end
  // synopsys translate_on
`endif


  ////////////////////////////////////////////////////////////////////////////////////////////
  //   ____ ___  ____  _____    ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //  / ___/ _ \|  _ \| ____|  / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  // | |  | | | | |_) |  _|   | |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  // | |__| |_| |  _ <| |___  | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //  \____\___/|_| \_\_____|  \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                                        //
  ////////////////////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    // Default values
    instr_req_o            = 1'b1;

    exc_ack_o              = 1'b0;
    exc_kill_o             = 1'b0;

    csr_save_if_o          = 1'b0;
    csr_save_id_o          = 1'b0;
    csr_restore_mret_id_o  = 1'b0;
    csr_restore_uret_id_o  = 1'b0;
    csr_save_cause_o       = 1'b0;

    exc_cause_o            = '0;
    exc_pc_mux_o           = EXC_PC_IRQ;
    trap_addr_mux_o        = TRAP_MACHINE;

    csr_cause_o            = '0;
    csr_irq_sec_o          = 1'b0;

    pc_mux_o               = PC_BOOT;
    pc_set_o               = 1'b0;
    jump_done              = jump_done_q;

    ctrl_fsm_ns            = ctrl_fsm_cs;

    ctrl_busy_o            = 1'b1;
    first_fetch_o          = 1'b0;

    halt_if_o              = 1'b0;
    halt_id_o              = 1'b0;
    dbg_ack_o              = 1'b0;
    irq_ack_o              = 1'b0;
    irq_id_o               = irq_id_ctrl_i;
    boot_done              = 1'b0;
    jump_in_dec            = jump_in_dec_i == BRANCH_JALR || jump_in_dec_i == BRANCH_JAL;
    branch_in_id           = jump_in_id_i == BRANCH_COND;
    irq_enable_int         =  ((u_IE_i | irq_sec_ctrl_i) & current_priv_lvl_i == PRIV_LVL_U) | (m_IE_i & current_priv_lvl_i == PRIV_LVL_M);

    // a trap towards the debug unit is generated when one of the
    // following conditions are true:
    // - ebreak instruction encountered
    // - single-stepping mode enabled
    // - illegal instruction exception and IIE bit is set
    // - IRQ and INTE bit is set and no exception is currently running
    // - Debuger requests halt
    dbg_trap_o             = 1'b0;

    unique case (ctrl_fsm_cs)
      // We were just reset, wait for fetch_enable
      RESET:
      begin
        is_decoding_o = 1'b0;

        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;

        if (fetch_enable_i == 1'b1)
          ctrl_fsm_ns = BOOT_SET;
        else if (dbg_req_i) begin
          // just go to debug even when we did not yet get a fetch enable
          // this means that the NPC will not be set yet
          ctrl_fsm_ns = DBG_SIGNAL;
        end
      end

      // copy boot address to instr fetch address
      BOOT_SET:
      begin
        is_decoding_o = 1'b0;
        instr_req_o   = 1'b1;
        pc_mux_o      = PC_BOOT;
        pc_set_o      = 1'b1;
        boot_done     = 1'b1;
        ctrl_fsm_ns = FIRST_FETCH;
      end

      WAIT_SLEEP:
      begin
        is_decoding_o = 1'b0;
        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;
        halt_if_o     = 1'b1;
        halt_id_o     = 1'b1;
        ctrl_fsm_ns   = SLEEP;
      end

      // instruction in if_stage is already valid
      SLEEP:
      begin
        // we begin execution when either fetch_enable is high or an
        // interrupt has arrived
        is_decoding_o = 1'b0;
        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;
        halt_if_o     = 1'b1;
        halt_id_o     = 1'b1;
        dbg_trap_o    = dbg_settings_i[DBG_SETS_SSTE];

        if (dbg_req_i) begin
          // debug request, now we need to check if we should stay sleeping or
          // go to normal processing later
          if (fetch_enable_i || irq_req_ctrl_i )
            ctrl_fsm_ns = DBG_SIGNAL;
          else
            ctrl_fsm_ns = DBG_SIGNAL_SLEEP;

        end else begin
          // no debug request incoming, normal execution flow
          if (fetch_enable_i || irq_req_ctrl_i )
          begin
            ctrl_fsm_ns  = FIRST_FETCH;
          end
        end
      end

      FIRST_FETCH:
      begin
        is_decoding_o = 1'b0;
        first_fetch_o = 1'b1;
        // Stall because of IF miss
        if ((id_ready_i == 1'b1) && (dbg_stall_i == 1'b0))
        begin
          ctrl_fsm_ns = DECODE;
        end

        // handle interrupts
        if (irq_req_ctrl_i & irq_enable_int) begin
          // This assumes that the pipeline is always flushed before
          // going to sleep.
          ctrl_fsm_ns = IRQ_TAKEN_IF;
          halt_if_o   = 1'b1;
          halt_id_o   = 1'b1;
        end
      end

      DECODE:
      begin

          if (branch_taken_ex_i)
          begin //taken branch
            // there is a branch in the EX stage that is taken

            is_decoding_o = 1'b0;

            pc_mux_o      = PC_BRANCH;
            pc_set_o      = 1'b1;
            dbg_trap_o    = dbg_settings_i[DBG_SETS_SSTE];
            // if we want to debug, flush the pipeline
            // the current_pc_if will take the value of the next instruction to
            // be executed (NPC)
            if (dbg_req_i)
            begin
              ctrl_fsm_ns = DBG_SIGNAL;
            end
          end  //taken branch

          // decode and execute instructions only if the current conditional
          // branch in the EX stage is either not taken, or there is no
          // conditional branch in the EX stage
          else if (instr_valid_i) //valid block or replay after interrupt speculation
          begin // now analyze the current instruction in the ID stage

            is_decoding_o = 1'b1;

            unique case(1'b1)

              //irq_req_ctrl_i comes from a FF in the interrupt controller
              //irq_enable_int: check again irq_enable_int because xIE could have changed
              irq_req_ctrl_i & irq_enable_int:
              begin
                //Serving the external interrupt
                halt_if_o     = 1'b1;
                halt_id_o     = 1'b1;
                ctrl_fsm_ns   = IRQ_FLUSH;
                //dbg_trap_o    = dbg_settings_i[DBG_SETS_IRQ];
              end

              default:
              begin

                exc_kill_o    = irq_req_ctrl_i ? 1'b1 : 1'b0;

                //decondig block
                unique case (1'b1)

                  jump_in_dec: begin
                  // handle unconditional jumps
                  // we can jump directly since we know the address already
                  // we don't need to worry about conditional branches here as they
                  // will be evaluated in the EX stage
                    pc_mux_o = PC_JUMP;
                    // if there is a jr stall, wait for it to be gone
                    if ((~jr_stall_o) && (~jump_done_q)) begin
                      pc_set_o    = 1'b1;
                      jump_done   = 1'b1;
                    end
                    dbg_trap_o    = dbg_settings_i[DBG_SETS_SSTE];
                  end
                  mret_insn_i | uret_insn_i | ecall_insn_i | pipe_flush_i | ebrk_insn_i | illegal_insn_i: begin
                    halt_if_o     = 1'b1;
                    halt_id_o     = 1'b1;
                    ctrl_fsm_ns   = FLUSH_EX;
                  end
                  csr_status_i: begin
                    halt_if_o     = 1'b1;
                    ctrl_fsm_ns   = id_ready_i ? FLUSH_EX : DECODE;
                  end
                  data_load_event_i: begin
                    ctrl_fsm_ns   = id_ready_i ? ELW_EXE : DECODE;
                    halt_if_o     = 1'b1;
                    dbg_trap_o    = dbg_settings_i[DBG_SETS_SSTE];
                  end
                  default:
                    dbg_trap_o    = dbg_settings_i[DBG_SETS_SSTE];
                endcase

                if (dbg_req_i)
                begin
                  // take care of debug
                  // branch conditional will be handled in next state
                  // halt pipeline immediately
                  halt_if_o = 1'b1;

                  // make sure the current instruction has been executed
                  // before changing state to non-decode
                  if (id_ready_i) begin
                    unique case(1'b1)
                      branch_in_id:
                        ctrl_fsm_ns = DBG_WAIT_BRANCH;
                      mret_insn_i | uret_insn_i | ecall_insn_i | pipe_flush_i | ebrk_insn_i | illegal_insn_i | csr_status_i | instr_multicycle_i:
                        //these instructions accept the Dbg after flushing
                        //for csr_status instructions, id_ready is 1 so they can change state to FLUSH_EX
                        ctrl_fsm_ns = FLUSH_EX;
                      default:
                        ctrl_fsm_ns = DBG_SIGNAL;
                    endcase
                  end
                end
              end //decondig block
            endcase
          end  //valid block
          else begin
            is_decoding_o = 1'b0;
          end
      end

      // a branch was in ID when a debug trap is hit
      DBG_WAIT_BRANCH:
      begin
        is_decoding_o = 1'b0;
        halt_if_o = 1'b1;

        if (branch_taken_ex_i) begin
          // there is a branch in the EX stage that is taken
          pc_mux_o = PC_BRANCH;
          pc_set_o = 1'b1;
        end

        ctrl_fsm_ns = DBG_SIGNAL;
      end

      // now we can signal to the debugger that our pipeline is empty and it
      // can examine our current state
      DBG_SIGNAL:
      begin
        is_decoding_o = 1'b0;

        dbg_ack_o   = 1'b1;
        halt_if_o   = 1'b1;
        ctrl_fsm_ns = DBG_WAIT;
      end

      DBG_SIGNAL_SLEEP:
      begin
        is_decoding_o = 1'b0;

        dbg_ack_o  = 1'b1;
        halt_if_o  = 1'b1;

        ctrl_fsm_ns = DBG_WAIT_SLEEP;
      end

      DBG_SIGNAL_ELW:
      begin
        is_decoding_o = 1'b0;

        dbg_ack_o  = 1'b1;
        halt_if_o  = 1'b1;

        ctrl_fsm_ns = DBG_WAIT_ELW;
      end

      DBG_WAIT_ELW:
      begin
        is_decoding_o = 1'b0;

        halt_if_o = 1'b1;

        if (dbg_jump_req_i) begin
          pc_mux_o     = PC_DBG_NPC;
          pc_set_o     = 1'b1;
          ctrl_fsm_ns  = DBG_WAIT;
        end

        if (dbg_stall_i == 1'b0) begin
          ctrl_fsm_ns = ELW_EXE;
        end
      end


      // The Debugger is active in this state
      // we wait until it is done and go back to SLEEP
      DBG_WAIT_SLEEP:
      begin
        is_decoding_o = 1'b0;

        halt_if_o = 1'b1;

        if (dbg_jump_req_i) begin
          pc_mux_o     = PC_DBG_NPC;
          pc_set_o     = 1'b1;
          ctrl_fsm_ns  = DBG_WAIT;
        end

        if (dbg_stall_i == 1'b0) begin
          ctrl_fsm_ns = SLEEP;
        end
      end

      // The Debugger is active in this state
      // we wait until it is done and go back to DECODE
      DBG_WAIT:
      begin
        is_decoding_o = 1'b0;

        halt_if_o = 1'b1;

        if (dbg_jump_req_i) begin
          pc_mux_o     = PC_DBG_NPC;
          pc_set_o     = 1'b1;
          ctrl_fsm_ns  = DBG_WAIT;
        end

        if (dbg_stall_i == 1'b0) begin
          //go to RESET if we used the debugger to initialize the core
          ctrl_fsm_ns = boot_done_q ? DECODE : RESET;
        end
      end

      // flush the pipeline, insert NOP into EX stage
      FLUSH_EX:
      begin
        is_decoding_o = 1'b0;

        halt_if_o = 1'b1;
        halt_id_o = 1'b1;
        if (ex_valid_i)
          //check done to prevent data harzard in the CSR registers
          ctrl_fsm_ns = FLUSH_WB;
      end

      IRQ_FLUSH:
      begin
        is_decoding_o = 1'b0;

        halt_if_o   = 1'b1;
        halt_id_o   = 1'b1;

        if(irq_req_ctrl_i & irq_enable_int) begin
          ctrl_fsm_ns = IRQ_TAKEN_ID;
        end else begin
          // we can go back to decode in case the IRQ is not taken (no ELW REPLAY)
          ctrl_fsm_ns  = DECODE;
        end
      end


      ELW_EXE:
      begin
        is_decoding_o = 1'b0;

        halt_if_o   = 1'b1;
        halt_id_o   = 1'b1;
        //if we are here, a elw is executing now in the EX stage
        //or if an interrupt has been received
        //the ID stage contains the PC_ID of the elw, therefore halt_id is set to invalid the instruction
        //If an interrupt occurs, we replay the ELW
        //No needs to check irq_int_req_i since in the EX stage there is only the elw, no CSR pendings
        if(id_ready_i)
          ctrl_fsm_ns = IRQ_FLUSH;
          // if from the ELW EXE we go to IRQ_FLUSH, it is assumed that if there was an IRQ req together with the grant and IE was valid, then
          // there must be no hazard due to xIE
        else if (dbg_req_i)
          ctrl_fsm_ns = DBG_SIGNAL_ELW;
        else
          ctrl_fsm_ns = ELW_EXE;
      end

      IRQ_TAKEN_ID:
      begin
        is_decoding_o = 1'b0;

        pc_set_o          = 1'b1;
        pc_mux_o          = PC_EXCEPTION;
        exc_pc_mux_o      = EXC_PC_IRQ;
        exc_cause_o       = {1'b0,irq_id_ctrl_i};

        csr_irq_sec_o     = irq_sec_ctrl_i;
        csr_save_cause_o  = 1'b1;
        csr_cause_o       = {1'b1,irq_id_ctrl_i};

        csr_save_id_o     = 1'b1;

        if(irq_sec_ctrl_i)
          trap_addr_mux_o  = TRAP_MACHINE;
        else
          trap_addr_mux_o  = current_priv_lvl_i == PRIV_LVL_U ? TRAP_USER : TRAP_MACHINE;

        irq_ack_o         = 1'b1;
        exc_ack_o         = 1'b1;
        ctrl_fsm_ns       = DECODE;
      end


      IRQ_TAKEN_IF:
      begin
        is_decoding_o = 1'b0;

        pc_set_o          = 1'b1;
        pc_mux_o          = PC_EXCEPTION;
        exc_pc_mux_o      = EXC_PC_IRQ;
        exc_cause_o       = {1'b0,irq_id_ctrl_i};

        csr_irq_sec_o     = irq_sec_ctrl_i;
        csr_save_cause_o  = 1'b1;
        csr_cause_o       = {1'b1,irq_id_ctrl_i};

        csr_save_if_o     = 1'b1;

        if(irq_sec_ctrl_i)
          trap_addr_mux_o  = TRAP_MACHINE;
        else
          trap_addr_mux_o  = current_priv_lvl_i == PRIV_LVL_U ? TRAP_USER : TRAP_MACHINE;

        irq_ack_o         = 1'b1;
        exc_ack_o         = 1'b1;

        ctrl_fsm_ns       = DECODE;
      end


      // flush the pipeline, insert NOP into EX and WB stage
      FLUSH_WB:
      begin
        is_decoding_o = 1'b0;

        halt_if_o = 1'b1;
        halt_id_o = 1'b1;

        unique case(1'b1)
          ecall_insn_i: begin
              //ecall
              pc_mux_o              = PC_EXCEPTION;
              pc_set_o              = 1'b1;
              csr_save_id_o         = 1'b1;
              csr_save_cause_o      = 1'b1;
              trap_addr_mux_o       = TRAP_MACHINE;
              exc_pc_mux_o          = EXC_PC_ECALL;
              exc_cause_o           = EXC_CAUSE_ECALL_MMODE;
              csr_cause_o           = current_priv_lvl_i == PRIV_LVL_U ? EXC_CAUSE_ECALL_UMODE : EXC_CAUSE_ECALL_MMODE;
              dbg_trap_o            = dbg_settings_i[DBG_SETS_ECALL] | dbg_settings_i[DBG_SETS_SSTE];
          end
          illegal_insn_i: begin
              //exceptions
              pc_mux_o              = PC_EXCEPTION;
              pc_set_o              = 1'b1;
              csr_save_id_o         = 1'b1;
              csr_save_cause_o      = 1'b1;
              trap_addr_mux_o       = TRAP_MACHINE;
              exc_pc_mux_o          = EXC_PC_ILLINSN;
              exc_cause_o           = EXC_CAUSE_ILLEGAL_INSN;
              csr_cause_o           = EXC_CAUSE_ILLEGAL_INSN;
              dbg_trap_o            = dbg_settings_i[DBG_SETS_EILL] | dbg_settings_i[DBG_SETS_SSTE];
          end
          mret_insn_i: begin
              //mret
              pc_mux_o              = PC_ERET;
              pc_set_o              = 1'b1;
              csr_restore_mret_id_o = 1'b1;
              dbg_trap_o            = dbg_settings_i[DBG_SETS_SSTE];
          end
          uret_insn_i: begin
              //uret
              pc_mux_o              = PC_ERET;
              pc_set_o              = 1'b1;
              csr_restore_uret_id_o = 1'b1;
              dbg_trap_o            = dbg_settings_i[DBG_SETS_SSTE];
          end
          ebrk_insn_i: begin
              dbg_trap_o    = dbg_settings_i[DBG_SETS_EBRK] | dbg_settings_i[DBG_SETS_SSTE];
              exc_cause_o   = EXC_CAUSE_BREAKPOINT;
          end
          csr_status_i: begin
              dbg_trap_o    = dbg_settings_i[DBG_SETS_SSTE];
          end
          pipe_flush_i: begin
              dbg_trap_o    = dbg_settings_i[DBG_SETS_SSTE];
          end
          default:;
        endcase

        if(fetch_enable_i) begin
          if(dbg_req_i)
            ctrl_fsm_ns = DBG_SIGNAL;
          else
            ctrl_fsm_ns = DECODE;
        end else begin
          if(dbg_req_i)
            ctrl_fsm_ns = DBG_SIGNAL_SLEEP;
          else
            ctrl_fsm_ns = (uret_insn_i | mret_insn_i | pipe_flush_i ) ? WAIT_SLEEP : DECODE;
        end

      end

      default: begin
        is_decoding_o = 1'b0;
        instr_req_o = 1'b0;
        ctrl_fsm_ns = RESET;
      end
    endcase
  end

  /////////////////////////////////////////////////////////////
  //  ____  _        _ _    ____            _             _  //
  // / ___|| |_ __ _| | |  / ___|___  _ __ | |_ _ __ ___ | | //
  // \___ \| __/ _` | | | | |   / _ \| '_ \| __| '__/ _ \| | //
  //  ___) | || (_| | | | | |__| (_) | | | | |_| | | (_) | | //
  // |____/ \__\__,_|_|_|  \____\___/|_| |_|\__|_|  \___/|_| //
  //                                                         //
  /////////////////////////////////////////////////////////////
  always_comb
  begin
    load_stall_o   = 1'b0;
    jr_stall_o     = 1'b0;
    deassert_we_o  = 1'b0;

    // deassert WE when the core is not decoding instructions
    if (~is_decoding_o)
      deassert_we_o = 1'b1;

    // deassert WE in case of illegal instruction
    if (illegal_insn_i)
      deassert_we_o = 1'b1;

    // Stall because of load operation
    if (
          ( (data_req_ex_i == 1'b1) && (regfile_we_ex_i == 1'b1) ||
           (wb_ready_i == 1'b0) && (regfile_we_wb_i == 1'b1)
          ) &&
          ( (reg_d_ex_is_reg_a_i == 1'b1) || (reg_d_ex_is_reg_b_i == 1'b1) || (reg_d_ex_is_reg_c_i == 1'b1) || (regfile_waddr_ex_i == regfile_alu_waddr_id_i))
       )
    begin
      deassert_we_o   = 1'b1;
      load_stall_o    = 1'b1;
    end

    // Stall because of jr path
    // - always stall if a result is to be forwarded to the PC
    // we don't care about in which state the ctrl_fsm is as we deassert_we
    // anyway when we are not in DECODE
    if ((jump_in_dec_i == BRANCH_JALR) &&
        (((regfile_we_wb_i == 1'b1) && (reg_d_wb_is_reg_a_i == 1'b1)) ||
         ((regfile_we_ex_i == 1'b1) && (reg_d_ex_is_reg_a_i == 1'b1)) ||
         ((regfile_alu_we_fw_i == 1'b1) && (reg_d_alu_is_reg_a_i == 1'b1))) )
    begin
      jr_stall_o      = 1'b1;
      deassert_we_o   = 1'b1;
    end
  end


  // stall because of misaligned data access
  assign misaligned_stall_o = data_misaligned_i;

  // APU dependency stalls (data hazards)
  assign apu_stall_o = apu_read_dep_i | (apu_write_dep_i & ~apu_en_i);

  // Forwarding control unit
  always_comb
  begin
    // default assignements
    operand_a_fw_mux_sel_o = SEL_REGFILE;
    operand_b_fw_mux_sel_o = SEL_REGFILE;
    operand_c_fw_mux_sel_o = SEL_REGFILE;

    // Forwarding WB -> ID
    if (regfile_we_wb_i == 1'b1)
    begin
      if (reg_d_wb_is_reg_a_i == 1'b1)
        operand_a_fw_mux_sel_o = SEL_FW_WB;
      if (reg_d_wb_is_reg_b_i == 1'b1)
        operand_b_fw_mux_sel_o = SEL_FW_WB;
      if (reg_d_wb_is_reg_c_i == 1'b1)
        operand_c_fw_mux_sel_o = SEL_FW_WB;
    end

    // Forwarding EX -> ID
    if (regfile_alu_we_fw_i == 1'b1)
    begin
     if (reg_d_alu_is_reg_a_i == 1'b1)
       operand_a_fw_mux_sel_o = SEL_FW_EX;
     if (reg_d_alu_is_reg_b_i == 1'b1)
       operand_b_fw_mux_sel_o = SEL_FW_EX;
     if (reg_d_alu_is_reg_c_i == 1'b1)
       operand_c_fw_mux_sel_o = SEL_FW_EX;
    end

    // for misaligned memory accesses
    if (data_misaligned_i)
    begin
      operand_a_fw_mux_sel_o  = SEL_FW_EX;
      operand_b_fw_mux_sel_o  = SEL_REGFILE;
    end else if (mult_multicycle_i) begin
      operand_c_fw_mux_sel_o  = SEL_FW_EX;
    end
  end

  // update registers
  always_ff @(posedge clk , negedge rst_n)
  begin : UPDATE_REGS
    if ( rst_n == 1'b0 )
    begin
      ctrl_fsm_cs    <= RESET;
      jump_done_q    <= 1'b0;
      boot_done_q    <= 1'b0;
    end
    else
    begin
      ctrl_fsm_cs    <= ctrl_fsm_ns;
      boot_done_q    <= boot_done | (~boot_done & boot_done_q);
      // clear when id is valid (no instruction incoming)
      jump_done_q    <= jump_done & (~id_ready_i);
    end
  end

  // Performance Counters
  assign perf_jump_o      = (jump_in_id_i == BRANCH_JAL || jump_in_id_i == BRANCH_JALR);
  assign perf_jr_stall_o  = jr_stall_o;
  assign perf_ld_stall_o  = load_stall_o;


  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
  // make sure that taken branches do not happen back-to-back, as this is not
  // possible without branch prediction in the IF stage
  `ifndef VERILATOR
  assert property (
    @(posedge clk) (branch_taken_ex_i) |=> (~branch_taken_ex_i) ) else $warning("Two branches back-to-back are taken");
  assert property (
    @(posedge clk) (~(dbg_req_i & irq_req_ctrl_i)) ) else $warning("Both dbg_req_i and irq_req_ctrl_i are active");
  `endif
endmodule // controller
