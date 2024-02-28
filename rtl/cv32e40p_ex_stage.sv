// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Execute stage                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Execution stage: Hosts ALU and MAC unit                    //
//                 ALU: computes additions/subtractions/comparisons           //
//                 MULT: computes normal multiplications                      //
//                 APU_DISP: offloads instructions to the shared unit.        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_ex_stage
  import cv32e40p_pkg::*;
  import cv32e40p_apu_core_pkg::*;
#(
    parameter COREV_PULP       = 0,
    parameter FPU              = 0,
    parameter APU_NARGS_CPU    = 3,
    parameter APU_WOP_CPU      = 6,
    parameter APU_NDSFLAGS_CPU = 15,
    parameter APU_NUSFLAGS_CPU = 5
) (
    input logic clk,
    input logic rst_n,

    // ALU signals from ID stage
    input alu_opcode_e        alu_operator_i,
    input logic        [31:0] alu_operand_a_i,
    input logic        [31:0] alu_operand_b_i,
    input logic        [31:0] alu_operand_c_i,
    input logic               alu_en_i,
    input logic        [ 4:0] bmask_a_i,
    input logic        [ 4:0] bmask_b_i,
    input logic        [ 1:0] imm_vec_ext_i,
    input logic        [ 1:0] alu_vec_mode_i,
    input logic               alu_is_clpx_i,
    input logic               alu_is_subrot_i,
    input logic        [ 1:0] alu_clpx_shift_i,

    // Multiplier signals
    input mul_opcode_e        mult_operator_i,
    input logic        [31:0] mult_operand_a_i,
    input logic        [31:0] mult_operand_b_i,
    input logic        [31:0] mult_operand_c_i,
    input logic               mult_en_i,
    input logic               mult_sel_subword_i,
    input logic        [ 1:0] mult_signed_mode_i,
    input logic        [ 4:0] mult_imm_i,

    input logic [31:0] mult_dot_op_a_i,
    input logic [31:0] mult_dot_op_b_i,
    input logic [31:0] mult_dot_op_c_i,
    input logic [ 1:0] mult_dot_signed_i,
    input logic        mult_is_clpx_i,
    input logic [ 1:0] mult_clpx_shift_i,
    input logic        mult_clpx_img_i,

    output logic mult_multicycle_o,

    input logic data_req_i,
    input logic data_rvalid_i,
    input logic data_misaligned_ex_i,
    input logic data_misaligned_i,

    input logic [1:0] ctrl_transfer_insn_in_dec_i,

    // FPU signals
    output logic fpu_fflags_we_o,
    output logic [APU_NUSFLAGS_CPU-1:0] fpu_fflags_o,

    // APU signals
    input logic                              apu_en_i,
    input logic [     APU_WOP_CPU-1:0]       apu_op_i,
    input logic [                 1:0]       apu_lat_i,
    input logic [   APU_NARGS_CPU-1:0][31:0] apu_operands_i,
    input logic [                 5:0]       apu_waddr_i,
    input logic [APU_NUSFLAGS_CPU-1:0]       apu_flags_i,

    input  logic [2:0][5:0] apu_read_regs_i,
    input  logic [2:0]      apu_read_regs_valid_i,
    output logic            apu_read_dep_o,
    output logic            apu_read_dep_for_jalr_o,
    input  logic [1:0][5:0] apu_write_regs_i,
    input  logic [1:0]      apu_write_regs_valid_i,
    output logic            apu_write_dep_o,

    output logic apu_perf_type_o,
    output logic apu_perf_cont_o,
    output logic apu_perf_wb_o,

    output logic apu_busy_o,
    output logic apu_ready_wb_o,

    // apu-interconnect
    // handshake signals
    output logic                           apu_req_o,
    input  logic                           apu_gnt_i,
    // request channel
    output logic [APU_NARGS_CPU-1:0][31:0] apu_operands_o,
    output logic [  APU_WOP_CPU-1:0]       apu_op_o,
    // response channel
    input  logic                           apu_rvalid_i,
    input  logic [             31:0]       apu_result_i,

    input logic        lsu_en_i,
    input logic [31:0] lsu_rdata_i,

    // input from ID stage
    input logic       branch_in_ex_i,
    input logic [5:0] regfile_alu_waddr_i,
    input logic       regfile_alu_we_i,

    // directly passed through to WB stage, not used in EX
    input logic       regfile_we_i,
    input logic [5:0] regfile_waddr_i,

    // CSR access
    input logic        csr_access_i,
    input logic [31:0] csr_rdata_i,

    // Output of EX stage pipeline
    output logic [ 5:0] regfile_waddr_wb_o,
    output logic        regfile_we_wb_o,
    output logic        regfile_we_wb_power_o,
    output logic [31:0] regfile_wdata_wb_o,

    // Forwarding ports : to ID stage
    output logic [ 5:0] regfile_alu_waddr_fw_o,
    output logic        regfile_alu_we_fw_o,
    output logic        regfile_alu_we_fw_power_o,
    output logic [31:0] regfile_alu_wdata_fw_o,  // forward to RF and ID/EX pipe, ALU & MUL

    // To IF: Jump and branch target and decision
    output logic [31:0] jump_target_o,
    output logic        branch_decision_o,

    // Stall Control
    input logic is_decoding_i, // Used to mask data Dependency inside the APU dispatcher in case of an istruction non valid
    input logic lsu_ready_ex_i,  // EX part of LSU is done
    input logic lsu_err_i,

    output logic ex_ready_o,  // EX stage ready for new data
    output logic ex_valid_o,  // EX stage gets new data
    input  logic wb_ready_i  // WB stage ready for new data
);

  logic [                31:0] alu_result;
  logic [                31:0] mult_result;
  logic                        alu_cmp_result;

  logic                        regfile_we_lsu;
  logic [                 5:0] regfile_waddr_lsu;

  logic                        wb_contention;
  logic                        wb_contention_lsu;

  logic                        alu_ready;
  logic                        mulh_active;
  logic                        mult_ready;

  // APU signals
  logic                        apu_valid;
  logic [                 5:0] apu_waddr;
  logic [                31:0] apu_result;
  logic                        apu_stall;
  logic                        apu_active;
  logic                        apu_singlecycle;
  logic                        apu_multicycle;
  logic                        apu_req;
  logic                        apu_gnt;

  logic                        apu_rvalid_q;
  logic [                31:0] apu_result_q;
  logic [APU_NUSFLAGS_CPU-1:0] apu_flags_q;

  // ALU write port mux
  always_comb begin
    regfile_alu_wdata_fw_o    = '0;
    regfile_alu_waddr_fw_o    = '0;
    regfile_alu_we_fw_o       = 1'b0;
    regfile_alu_we_fw_power_o = 1'b0;
    wb_contention             = 1'b0;

    // APU single cycle operations, and multicycle operations (> 2cycles) are written back on ALU port
    if (apu_valid & (apu_singlecycle | apu_multicycle)) begin
      regfile_alu_we_fw_o       = 1'b1;
      regfile_alu_we_fw_power_o = 1'b1;
      regfile_alu_waddr_fw_o    = apu_waddr;
      regfile_alu_wdata_fw_o    = apu_result;

      if (regfile_alu_we_i & ~apu_en_i) begin
        wb_contention = 1'b1;
      end
    end else begin
      regfile_alu_we_fw_o = regfile_alu_we_i & ~apu_en_i;
      regfile_alu_we_fw_power_o = (COREV_PULP == 0) ? regfile_alu_we_i & ~apu_en_i : 
                                                     regfile_alu_we_i & ~apu_en_i &
                                                     mult_ready & alu_ready & lsu_ready_ex_i;
      regfile_alu_waddr_fw_o = regfile_alu_waddr_i;
      if (alu_en_i) regfile_alu_wdata_fw_o = alu_result;
      if (mult_en_i) regfile_alu_wdata_fw_o = mult_result;
      if (csr_access_i) regfile_alu_wdata_fw_o = csr_rdata_i;
    end
  end

  // LSU write port mux
  always_comb begin
    regfile_we_wb_o       = 1'b0;
    regfile_we_wb_power_o = 1'b0;
    regfile_waddr_wb_o    = regfile_waddr_lsu;
    regfile_wdata_wb_o    = lsu_rdata_i;
    wb_contention_lsu     = 1'b0;

    if (regfile_we_lsu) begin
      regfile_we_wb_o       = 1'b1;
      regfile_we_wb_power_o = (COREV_PULP == 0) ? 1'b1 : ~data_misaligned_ex_i & wb_ready_i;
      if (apu_valid & (!apu_singlecycle & !apu_multicycle)) begin
        wb_contention_lsu = 1'b1;
      end
      // APU two-cycle operations are written back on LSU port
    end else if (apu_valid & (!apu_singlecycle & !apu_multicycle)) begin
      regfile_we_wb_o       = 1'b1;
      regfile_we_wb_power_o = 1'b1;
      regfile_waddr_wb_o    = apu_waddr;
      regfile_wdata_wb_o    = apu_result;
    end
  end

  // branch handling
  assign branch_decision_o = alu_cmp_result;
  assign jump_target_o     = alu_operand_c_i;


  ////////////////////////////
  //     _    _    _   _    //
  //    / \  | |  | | | |   //
  //   / _ \ | |  | | | |   //
  //  / ___ \| |__| |_| |   //
  // /_/   \_\_____\___/    //
  //                        //
  ////////////////////////////

  cv32e40p_alu alu_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .enable_i   (alu_en_i),
      .operator_i (alu_operator_i),
      .operand_a_i(alu_operand_a_i),
      .operand_b_i(alu_operand_b_i),
      .operand_c_i(alu_operand_c_i),

      .vector_mode_i(alu_vec_mode_i),
      .bmask_a_i    (bmask_a_i),
      .bmask_b_i    (bmask_b_i),
      .imm_vec_ext_i(imm_vec_ext_i),

      .is_clpx_i   (alu_is_clpx_i),
      .clpx_shift_i(alu_clpx_shift_i),
      .is_subrot_i (alu_is_subrot_i),

      .result_o           (alu_result),
      .comparison_result_o(alu_cmp_result),

      .ready_o   (alu_ready),
      .ex_ready_i(ex_ready_o)
  );


  ////////////////////////////////////////////////////////////////
  //  __  __ _   _ _   _____ ___ ____  _     ___ _____ ____     //
  // |  \/  | | | | | |_   _|_ _|  _ \| |   |_ _| ____|  _ \    //
  // | |\/| | | | | |   | |  | || |_) | |    | ||  _| | |_) |   //
  // | |  | | |_| | |___| |  | ||  __/| |___ | || |___|  _ <    //
  // |_|  |_|\___/|_____|_| |___|_|   |_____|___|_____|_| \_\   //
  //                                                            //
  ////////////////////////////////////////////////////////////////

  cv32e40p_mult mult_i (
      .clk  (clk),
      .rst_n(rst_n),

      .enable_i  (mult_en_i),
      .operator_i(mult_operator_i),

      .short_subword_i(mult_sel_subword_i),
      .short_signed_i (mult_signed_mode_i),

      .op_a_i(mult_operand_a_i),
      .op_b_i(mult_operand_b_i),
      .op_c_i(mult_operand_c_i),
      .imm_i (mult_imm_i),

      .dot_op_a_i  (mult_dot_op_a_i),
      .dot_op_b_i  (mult_dot_op_b_i),
      .dot_op_c_i  (mult_dot_op_c_i),
      .dot_signed_i(mult_dot_signed_i),
      .is_clpx_i   (mult_is_clpx_i),
      .clpx_shift_i(mult_clpx_shift_i),
      .clpx_img_i  (mult_clpx_img_i),

      .result_o(mult_result),

      .multicycle_o (mult_multicycle_o),
      .mulh_active_o(mulh_active),
      .ready_o      (mult_ready),
      .ex_ready_i   (ex_ready_o)
  );

  generate
    if (FPU == 1) begin : gen_apu
      ////////////////////////////////////////////////////
      //     _    ____  _   _   ____ ___ ____  ____     //
      //    / \  |  _ \| | | | |  _ \_ _/ ___||  _ \    //
      //   / _ \ | |_) | | | | | | | | |\___ \| |_) |   //
      //  / ___ \|  __/| |_| | | |_| | | ___) |  __/    //
      // /_/   \_\_|    \___/  |____/___|____/|_|       //
      //                                                //
      ////////////////////////////////////////////////////

      cv32e40p_apu_disp apu_disp_i (
          .clk_i (clk),
          .rst_ni(rst_n),

          .enable_i   (apu_en_i),
          .apu_lat_i  (apu_lat_i),
          .apu_waddr_i(apu_waddr_i),

          .apu_waddr_o      (apu_waddr),
          .apu_multicycle_o (apu_multicycle),
          .apu_singlecycle_o(apu_singlecycle),

          .active_o(apu_active),
          .stall_o (apu_stall),

          .is_decoding_i      (is_decoding_i),
          .read_regs_i        (apu_read_regs_i),
          .read_regs_valid_i  (apu_read_regs_valid_i),
          .read_dep_o         (apu_read_dep_o),
          .read_dep_for_jalr_o(apu_read_dep_for_jalr_o),
          .write_regs_i       (apu_write_regs_i),
          .write_regs_valid_i (apu_write_regs_valid_i),
          .write_dep_o        (apu_write_dep_o),

          .perf_type_o(apu_perf_type_o),
          .perf_cont_o(apu_perf_cont_o),

          // apu-interconnect
          // handshake signals
          .apu_req_o   (apu_req),
          .apu_gnt_i   (apu_gnt),
          // response channel
          .apu_rvalid_i(apu_valid)
      );

      assign apu_perf_wb_o  = wb_contention | wb_contention_lsu;
      assign apu_ready_wb_o = ~(apu_active | apu_en_i | apu_stall) | apu_valid;

      ///////////////////////////////////////
      // APU result memorization Register  //
      ///////////////////////////////////////
      always_ff @(posedge clk, negedge rst_n) begin : APU_Result_Memorization
        if (~rst_n) begin
          apu_rvalid_q <= 1'b0;
          apu_result_q <= 'b0;
          apu_flags_q  <= 'b0;
        end else begin
          if (apu_rvalid_i && apu_multicycle &&
              (data_misaligned_i || data_misaligned_ex_i ||
               ((data_req_i || data_rvalid_i) && regfile_alu_we_i) ||
               (mulh_active && (mult_operator_i == MUL_H)) ||
               ((ctrl_transfer_insn_in_dec_i == BRANCH_JALR) &&
                regfile_alu_we_i && ~apu_read_dep_for_jalr_o))) begin
            apu_rvalid_q <= 1'b1;
            apu_result_q <= apu_result_i;
            apu_flags_q  <= apu_flags_i;
          end else if (apu_rvalid_q && !(data_misaligned_i || data_misaligned_ex_i ||
                                         ((data_req_i || data_rvalid_i) && regfile_alu_we_i) ||
                                         (mulh_active && (mult_operator_i == MUL_H)) ||
                                         ((ctrl_transfer_insn_in_dec_i == BRANCH_JALR) &&
                                          regfile_alu_we_i && ~apu_read_dep_for_jalr_o))) begin
            apu_rvalid_q <= 1'b0;
          end
        end
      end

      assign apu_req_o = apu_req;
      assign apu_gnt = apu_gnt_i;
      assign apu_valid = (apu_multicycle && (data_misaligned_i || data_misaligned_ex_i ||
                                             ((data_req_i || data_rvalid_i) && regfile_alu_we_i) ||
                                             (mulh_active && (mult_operator_i == MUL_H)) ||
                                             ((ctrl_transfer_insn_in_dec_i == BRANCH_JALR) &&
                                              regfile_alu_we_i && ~apu_read_dep_for_jalr_o)))
                         ? 1'b0 : (apu_rvalid_i || apu_rvalid_q);
      assign apu_operands_o = apu_operands_i;
      assign apu_op_o = apu_op_i;
      assign apu_result = apu_rvalid_q ? apu_result_q : apu_result_i;
      assign fpu_fflags_we_o = apu_valid;
      assign fpu_fflags_o = apu_rvalid_q ? apu_flags_q : apu_flags_i;
    end else begin : gen_no_apu
      // default assignements for the case when no FPU/APU is attached.
      assign apu_req_o               = '0;
      assign apu_operands_o[0]       = '0;
      assign apu_operands_o[1]       = '0;
      assign apu_operands_o[2]       = '0;
      assign apu_op_o                = '0;
      assign apu_req                 = 1'b0;
      assign apu_gnt                 = 1'b0;
      assign apu_result              = 32'b0;
      assign apu_valid               = 1'b0;
      assign apu_waddr               = 6'b0;
      assign apu_stall               = 1'b0;
      assign apu_active              = 1'b0;
      assign apu_ready_wb_o          = 1'b1;
      assign apu_perf_wb_o           = 1'b0;
      assign apu_perf_cont_o         = 1'b0;
      assign apu_perf_type_o         = 1'b0;
      assign apu_singlecycle         = 1'b0;
      assign apu_multicycle          = 1'b0;
      assign apu_read_dep_o          = 1'b0;
      assign apu_read_dep_for_jalr_o = 1'b0;
      assign apu_write_dep_o         = 1'b0;
      assign fpu_fflags_o            = '0;
      assign fpu_fflags_we_o         = '0;
    end
  endgenerate

  assign apu_busy_o = apu_active;

  ///////////////////////////////////////
  // EX/WB Pipeline Register           //
  ///////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n) begin : EX_WB_Pipeline_Register
    if (~rst_n) begin
      regfile_waddr_lsu <= '0;
      regfile_we_lsu    <= 1'b0;
    end else begin
      if (ex_valid_o) // wb_ready_i is implied
      begin
        regfile_we_lsu <= regfile_we_i & ~lsu_err_i;
        if (regfile_we_i & ~lsu_err_i) begin
          regfile_waddr_lsu <= regfile_waddr_i;
        end
      end else if (wb_ready_i) begin
        // we are ready for a new instruction, but there is none available,
        // so we just flush the current one out of the pipe
        regfile_we_lsu <= 1'b0;
      end
    end
  end

  // As valid always goes to the right and ready to the left, and we are able
  // to finish branches without going to the WB stage, ex_valid does not
  // depend on ex_ready.
  assign ex_ready_o = (~apu_stall & alu_ready & mult_ready & lsu_ready_ex_i
                       & wb_ready_i & ~wb_contention) | (branch_in_ex_i);
  assign ex_valid_o = (apu_valid | alu_en_i | mult_en_i | csr_access_i | lsu_en_i)
                       & (alu_ready & mult_ready & lsu_ready_ex_i & wb_ready_i);

endmodule
