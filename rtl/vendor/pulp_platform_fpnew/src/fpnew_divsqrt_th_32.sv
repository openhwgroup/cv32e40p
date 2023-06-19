// Copyright 2019-2022 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// SPDX-License-Identifier: SHL-0.51

// Authors: Stefan Mach <smach@iis.ee.ethz.ch>
//          Luca Bertaccini <lbertaccini@iis.ee.ethz.ch>
//          Jiang Lannan <jiangl@ethz.ch>
//          Kexin Li <likexi@ethz.ch>

`include "common_cells/registers.svh"

module fpnew_divsqrt_th_32 #(
  // FP32-only DivSqrt
  // FPU configuration
  parameter int unsigned             NumPipeRegs = 0,
  parameter fpnew_pkg::pipe_config_t PipeConfig  = fpnew_pkg::BEFORE,
  parameter type                     TagType     = logic,
  parameter type                     AuxType     = logic,
  // Do not change
  localparam int unsigned WIDTH       = 32,
  localparam int unsigned NUM_FORMATS = fpnew_pkg::NUM_FP_FORMATS,
  localparam int unsigned ExtRegEnaWidth = NumPipeRegs == 0 ? 1 : NumPipeRegs
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  // Input signals
  input  logic [1:0][WIDTH-1:0]       operands_i, // 2 operands
  input  logic [NUM_FORMATS-1:0][1:0] is_boxed_i, // 2 operands
  input  fpnew_pkg::roundmode_e       rnd_mode_i,
  input  fpnew_pkg::operation_e       op_i,
  input  TagType                      tag_i,
  input  logic                        mask_i,
  input  AuxType                      aux_i,
  // Input Handshake
  input  logic                        in_valid_i,
  output logic                        in_ready_o,
  input  logic                        flush_i,
  // Output signals
  output logic [WIDTH-1:0]            result_o,
  output fpnew_pkg::status_t          status_o,
  output logic                        extension_bit_o,
  output TagType                      tag_o,
  output logic                        mask_o,
  output AuxType                      aux_o,
  // Output handshake
  output logic                        out_valid_o,
  input  logic                        out_ready_i,
  // Indication of valid data in flight
  output logic                        busy_o,
  // External register enable override
  input  logic [ExtRegEnaWidth-1:0]   reg_ena_i
);

  // ----------
  // Constants
  // ----------
  // Pipelines
  localparam NUM_INP_REGS = (PipeConfig == fpnew_pkg::BEFORE)
                            ? NumPipeRegs
                            : (PipeConfig == fpnew_pkg::DISTRIBUTED
                               ? (NumPipeRegs / 2) // Last to get distributed regs
                               : 0); // no regs here otherwise
  localparam NUM_OUT_REGS = (PipeConfig == fpnew_pkg::AFTER || PipeConfig == fpnew_pkg::INSIDE)
                            ? NumPipeRegs
                            : (PipeConfig == fpnew_pkg::DISTRIBUTED
                               ? ((NumPipeRegs + 1) / 2) // First to get distributed regs
                               : 0); // no regs here otherwise

  // ---------------
  // Input pipeline
  // ---------------
  // Selected pipeline output signals as non-arrays
  logic [1:0][WIDTH-1:0] operands_q;
  fpnew_pkg::roundmode_e rnd_mode_q;
  fpnew_pkg::operation_e op_q;
  logic                  in_valid_q;

  // Input pipeline signals, index i holds signal after i register stages
  logic                  [0:NUM_INP_REGS][1:0][WIDTH-1:0]       inp_pipe_operands_q;
  fpnew_pkg::roundmode_e [0:NUM_INP_REGS]                       inp_pipe_rnd_mode_q;
  fpnew_pkg::operation_e [0:NUM_INP_REGS]                       inp_pipe_op_q;
  TagType                [0:NUM_INP_REGS]                       inp_pipe_tag_q;
  logic                  [0:NUM_INP_REGS]                       inp_pipe_mask_q;
  AuxType                [0:NUM_INP_REGS]                       inp_pipe_aux_q;
  logic                  [0:NUM_INP_REGS]                       inp_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_INP_REGS] inp_pipe_ready;

  // Input stage: First element of pipeline is taken from inputs
  assign inp_pipe_operands_q[0] = operands_i;
  assign inp_pipe_rnd_mode_q[0] = rnd_mode_i;
  assign inp_pipe_op_q[0]       = op_i;
  assign inp_pipe_tag_q[0]      = tag_i;
  assign inp_pipe_mask_q[0]     = mask_i;
  assign inp_pipe_aux_q[0]      = aux_i;
  assign inp_pipe_valid_q[0]    = in_valid_i;
  // Input stage: Propagate pipeline ready signal to updtream circuitry
  assign in_ready_o = inp_pipe_ready[0];
  // Generate the register stages
  for (genvar i = 0; i < NUM_INP_REGS; i++) begin : gen_input_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign inp_pipe_ready[i] = inp_pipe_ready[i+1] | ~inp_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(inp_pipe_valid_q[i+1], inp_pipe_valid_q[i], inp_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipleine ready and a valid data item is present
    assign reg_ena = (inp_pipe_ready[i] & inp_pipe_valid_q[i]) | reg_ena_i[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(inp_pipe_operands_q[i+1], inp_pipe_operands_q[i], reg_ena, '0)
    `FFL(inp_pipe_rnd_mode_q[i+1], inp_pipe_rnd_mode_q[i], reg_ena, fpnew_pkg::RNE)
    `FFL(inp_pipe_op_q[i+1],       inp_pipe_op_q[i],       reg_ena, fpnew_pkg::FMADD)
    `FFL(inp_pipe_tag_q[i+1],      inp_pipe_tag_q[i],      reg_ena, TagType'('0))
    `FFL(inp_pipe_mask_q[i+1],     inp_pipe_mask_q[i],     reg_ena, '0)
    `FFL(inp_pipe_aux_q[i+1],      inp_pipe_aux_q[i],      reg_ena, AuxType'('0))
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign operands_q = inp_pipe_operands_q[NUM_INP_REGS];
  assign rnd_mode_q = inp_pipe_rnd_mode_q[NUM_INP_REGS];
  assign op_q       = inp_pipe_op_q[NUM_INP_REGS];
  assign in_valid_q = inp_pipe_valid_q[NUM_INP_REGS];

  // ------------
  // Control FSM
  // ------------
  logic in_ready;               // input handshake with upstream
  logic div_op, sqrt_op;        // input signalling with unit
  logic unit_ready_q, unit_done;  // status signals from unit instance
  logic op_starting;            // high in the cycle a new operation starts
  logic out_valid, out_ready;   // output handshake with downstream
  logic hold_result;            // whether to put result into hold register
  logic data_is_held;           // data in hold register is valid
  logic unit_busy;              // valid data in flight
  // FSM states
  typedef enum logic [1:0] {IDLE, BUSY, HOLD} fsm_state_e;
  fsm_state_e state_q, state_d;

  // Operations are gated by the FSM ready. Invalid input ops run a sqrt to not lose illegal instr.
  assign div_op   = in_valid_q & (op_q == fpnew_pkg::DIV) & in_ready & ~flush_i;  //in_ready delete, valid independent of ready
  assign sqrt_op  = in_valid_q & (op_q == fpnew_pkg::SQRT) & in_ready & ~flush_i;
  assign op_starting = div_op | sqrt_op;  //start computing or handshake, modify tb handshake right

  logic fdsu_fpu_ex1_stall, fdsu_fpu_ex1_stall_q;
  logic div_op_d, div_op_q;
  logic sqrt_op_d, sqrt_op_q;

  assign div_op_d  = (fdsu_fpu_ex1_stall) ? div_op  : 1'b0;
  assign sqrt_op_d = (fdsu_fpu_ex1_stall) ? sqrt_op : 1'b0;

  `FFL(fdsu_fpu_ex1_stall_q, fdsu_fpu_ex1_stall, 1'b1, '0)
  `FFL(div_op_q, div_op_d, 1'b1, '0)
  `FFL(sqrt_op_q, sqrt_op_d, 1'b1, '0)

  // FSM to safely apply and receive data from DIVSQRT unit
  always_comb begin : flag_fsm
    // Default assignments
    in_ready     = 1'b0;
    out_valid    = 1'b0;
    hold_result  = 1'b0;
    data_is_held = 1'b0;
    unit_busy    = 1'b0;
    state_d      = state_q;
    inp_pipe_ready[NUM_INP_REGS] = unit_ready_q;

    unique case (state_q)
      // Waiting for work
      IDLE: begin
        // in_ready = 1'b1; // we're ready
        in_ready = unit_ready_q;  //***
        if (in_valid_q && unit_ready_q) begin // New work arrives
          inp_pipe_ready[NUM_INP_REGS] = unit_ready_q && !fdsu_fpu_ex1_stall;
          state_d = BUSY; // go into processing state
        end
      end
      // Operation in progress
      BUSY: begin
        inp_pipe_ready[NUM_INP_REGS] = fdsu_fpu_ex1_stall_q;
        unit_busy = 1'b1; // data in flight
        // If the unit is done with processing
        if (unit_done) begin
          out_valid = 1'b1; // try to commit result downstream
          // If downstream accepts our result
          if (out_ready) begin
            state_d = IDLE; // we anticipate going back to idling..
            if (in_valid_q && unit_ready_q) begin // ..unless new work comes in
              in_ready = 1'b1; // we acknowledge the instruction
              state_d  = BUSY; // and stay busy with it
            end
          // Otherwise if downstream is not ready for the result
          end else begin
            hold_result = 1'b1; // activate the hold register
            state_d     = HOLD; // wait for the pipeline to take the data
          end
        end
      end
      // Waiting with valid result for downstream
      HOLD: begin
        unit_busy    = 1'b1; // data in flight
        data_is_held = 1'b1; // data in hold register is valid
        out_valid    = 1'b1; // try to commit result downstream
        // If the result is accepted by downstream
        if (out_ready) begin
          state_d = IDLE; // go back to idle..
          if (in_valid_q && unit_ready_q) begin // ..unless new work comes in
            in_ready = 1'b1; // acknowledge the new transaction
            state_d  = BUSY; // will be busy with the next instruction
          end
        end
      end
      // fall into idle state otherwise
      default: state_d = IDLE;
    endcase

    // Flushing overrides the other actions
    if (flush_i) begin
      unit_busy = 1'b0; // data is invalidated
      out_valid = 1'b0; // cancel any valid data
      state_d   = IDLE; // go to default state
    end
  end

  // FSM status register (asynch active low reset)
  `FF(state_q, state_d, IDLE)

  // Hold additional information while the operation is in progress
  TagType result_tag_q;
  AuxType result_aux_q;
  logic   result_mask_q;

  // Fill the registers everytime a valid operation arrives (load FF, active low asynch rst)
  `FFL(result_tag_q,  inp_pipe_tag_q[NUM_INP_REGS],  op_starting, '0)
  `FFL(result_mask_q, inp_pipe_mask_q[NUM_INP_REGS], op_starting, '0)
  `FFL(result_aux_q,  inp_pipe_aux_q[NUM_INP_REGS],  op_starting, '0)

  // -----------------
  // DIVSQRT instance
  // -----------------
  logic [WIDTH-1:0]   unit_result, held_result_q;
  fpnew_pkg::status_t unit_status, held_status_q;

  // thead define fdsu module's input and output
  logic        ctrl_fdsu_ex1_sel;
  logic        fdsu_fpu_ex1_cmplt;
  logic  [4:0] fdsu_fpu_ex1_fflags;
  logic  [7:0] fdsu_fpu_ex1_special_sel;
  logic  [3:0] fdsu_fpu_ex1_special_sign;
  logic        fdsu_fpu_no_op;
  logic  [2:0] idu_fpu_ex1_eu_sel;
  logic [31:0] fdsu_frbus_data;
  logic  [4:0] fdsu_frbus_fflags;
  logic        fdsu_frbus_wb_vld;

  // dp
  logic [31:0] dp_frbus_ex2_data;
  logic  [4:0] dp_frbus_ex2_fflags;
  logic  [2:0] dp_xx_ex1_cnan;
  logic  [2:0] dp_xx_ex1_id;
  logic  [2:0] dp_xx_ex1_inf;
  logic  [2:0] dp_xx_ex1_norm;
  logic  [2:0] dp_xx_ex1_qnan;
  logic  [2:0] dp_xx_ex1_snan;
  logic  [2:0] dp_xx_ex1_zero;
  logic        ex2_inst_wb;
  logic        ex2_inst_wb_vld_d, ex2_inst_wb_vld_q;

  // frbus
  logic [31:0] fpu_idu_fwd_data;
  logic  [4:0] fpu_idu_fwd_fflags;
  logic        fpu_idu_fwd_vld;

  logic unit_ready_d;

  // unit_ready_q related to state machine, different under special and normal cases.
  always_comb begin
    if(op_starting && unit_ready_q) begin
      if(ex2_inst_wb && ex2_inst_wb_vld_q) begin
        unit_ready_d = 1'b1;
      end else begin
        unit_ready_d = 1'b0;
      end
    end else if(fpu_idu_fwd_vld | flush_i) begin
      unit_ready_d = 1'b1;
    end else begin
      unit_ready_d = unit_ready_q;
    end
  end

  `FFL(unit_ready_q, unit_ready_d, 1'b1, 1'b1)

  // determine input of time to select operands
  always_comb begin
    ctrl_fdsu_ex1_sel = 1'b0;
    idu_fpu_ex1_eu_sel = 3'h0;
    if (op_starting) begin  // time to start calculation
      ctrl_fdsu_ex1_sel = 1'b1;  // time to select operands
      idu_fpu_ex1_eu_sel = 3'h4; // time to select operands, only idu_fpu_ex1_eu_sel_i[2] works in fdsu module
    end else if (fdsu_fpu_ex1_stall_q) begin
      ctrl_fdsu_ex1_sel = 1'b1;  // time to select operands
      idu_fpu_ex1_eu_sel = 3'h4; // time to select operands, only idu_fpu_ex1_eu_sel_i[2] works in fdsu module
    end else begin
      ctrl_fdsu_ex1_sel = 1'b0;
      idu_fpu_ex1_eu_sel = 3'h0;
    end
  end

  pa_fdsu_top i_divsqrt_thead (
   .cp0_fpu_icg_en                ( 1'b0               ),  // input clock gate enable in gated_clk_cell, active 0.
   .cp0_fpu_xx_dqnan              ( 1'b0               ),  // When dqnan = 0, QNAN (0x7fc00000).
   .cp0_yy_clk_en                 ( 1'b1               ),  // clock enable in gated_clk_cell, active 1.
   .cpurst_b                      ( rst_ni             ),  // If negedge cpu reset, all state machines reset to IDLE.
   .ctrl_fdsu_ex1_sel             ( ctrl_fdsu_ex1_sel  ),  // select operands
   .ctrl_xx_ex1_cmplt_dp          ( ctrl_fdsu_ex1_sel  ),  // complete datapath
   .ctrl_xx_ex1_inst_vld          ( ctrl_fdsu_ex1_sel  ),  // instance valid
   .ctrl_xx_ex1_stall             ( fdsu_fpu_ex1_stall ),
   .ctrl_xx_ex1_warm_up           ( 1'b0               ),
   .ctrl_xx_ex2_warm_up           ( 1'b0               ),
   .ctrl_xx_ex3_warm_up           ( 1'b0               ),
   .dp_xx_ex1_cnan                ( dp_xx_ex1_cnan     ),  // Special input type determination
   .dp_xx_ex1_id                  ( dp_xx_ex1_id       ),
   .dp_xx_ex1_inf                 ( dp_xx_ex1_inf      ),
   .dp_xx_ex1_qnan                ( dp_xx_ex1_qnan     ),
   .dp_xx_ex1_rm                  ( rnd_mode_q         ),  // rounding mode
   .dp_xx_ex1_snan                ( dp_xx_ex1_snan     ),
   .dp_xx_ex1_zero                ( dp_xx_ex1_zero     ),
   .fdsu_fpu_debug_info           (                    ),  // output, not used
   .fdsu_fpu_ex1_cmplt            ( fdsu_fpu_ex1_cmplt ),  // output, ctrl_xx_ex1_cmplt_dp && idu_fpu_ex1_eu_sel_i[2]
   .fdsu_fpu_ex1_cmplt_dp         (                    ),  // output, not used
   .fdsu_fpu_ex1_fflags           ( fdsu_fpu_ex1_fflags       ),  // output, special case fflags
   .fdsu_fpu_ex1_special_sel      ( fdsu_fpu_ex1_special_sel  ),  // output, special case type selection
   .fdsu_fpu_ex1_special_sign     ( fdsu_fpu_ex1_special_sign ),  // output, special case sign determination
   .fdsu_fpu_ex1_stall            ( fdsu_fpu_ex1_stall        ),  // output, determine whether stall in ex1
   .fdsu_fpu_no_op                ( fdsu_fpu_no_op            ),  // output, if Write Back SM and fdsu SM no operation, fdsu_fpu_no_op = 1; Otherwise if busy, fdsu_fpu_no_op = 0. (not used)
   .fdsu_frbus_data               ( fdsu_frbus_data           ),  // output, normal case result
   .fdsu_frbus_fflags             ( fdsu_frbus_fflags         ),  // output, normal case fflags
   .fdsu_frbus_freg               (                           ),  // output, determined by input idu_fpu_ex1_dst_freg
   .fdsu_frbus_wb_vld             ( fdsu_frbus_wb_vld         ),  // output, determine whether write back valid
   .forever_cpuclk                ( clk_i                     ),
   .frbus_fdsu_wb_grant           ( fdsu_frbus_wb_vld         ),  // input is fdsu_frbus_wb_vld
   .idu_fpu_ex1_dst_freg          ( 5'h0f                     ),  // register index to write back (not used)
   .idu_fpu_ex1_eu_sel            ( idu_fpu_ex1_eu_sel        ),  // time to select operands
   .idu_fpu_ex1_func              ( {8'b0, div_op | div_op_q, sqrt_op | sqrt_op_q} ),
   .idu_fpu_ex1_srcf0             ( operands_q[0][31:0]       ),  // the first operand
   .idu_fpu_ex1_srcf1             ( operands_q[1][31:0]       ),  // the second operand
   .pad_yy_icg_scan_en            ( 1'b0                      ),  // input of core_top, set to 1'b0 from the beginning to end
   .rtu_xx_ex1_cancel             ( 1'b0                      ),
   .rtu_xx_ex2_cancel             ( 1'b0                      ),
   .rtu_yy_xx_async_flush         ( flush_i                   ),
   .rtu_yy_xx_flush               ( 1'b0                      )
  );

  pa_fpu_dp  x_pa_fpu_dp (
    .cp0_fpu_icg_en              ( 1'b0                       ),
    .cp0_fpu_xx_rm               ( rnd_mode_q                 ),
    .cp0_yy_clk_en               ( 1'b1                       ),
    .ctrl_xx_ex1_inst_vld        ( ctrl_fdsu_ex1_sel          ),
    .ctrl_xx_ex1_stall           ( 1'b0                       ),
    .ctrl_xx_ex1_warm_up         ( 1'b0                       ),
    .dp_frbus_ex2_data           ( dp_frbus_ex2_data          ),  // output
    .dp_frbus_ex2_fflags         ( dp_frbus_ex2_fflags        ),  // output
    .dp_xx_ex1_cnan              ( dp_xx_ex1_cnan             ),  // output
    .dp_xx_ex1_id                ( dp_xx_ex1_id               ),  // output
    .dp_xx_ex1_inf               ( dp_xx_ex1_inf              ),  // output
    .dp_xx_ex1_norm              ( dp_xx_ex1_norm             ),  // output
    .dp_xx_ex1_qnan              ( dp_xx_ex1_qnan             ),  // output
    .dp_xx_ex1_snan              ( dp_xx_ex1_snan             ),  // output
    .dp_xx_ex1_zero              ( dp_xx_ex1_zero             ),  // output
    .ex2_inst_wb                 ( ex2_inst_wb                ),  // output
    .fdsu_fpu_ex1_fflags         ( fdsu_fpu_ex1_fflags        ),
    .fdsu_fpu_ex1_special_sel    ( fdsu_fpu_ex1_special_sel   ),
    .fdsu_fpu_ex1_special_sign   ( fdsu_fpu_ex1_special_sign  ),
    .forever_cpuclk              ( clk_i                      ),
    .idu_fpu_ex1_eu_sel          ( idu_fpu_ex1_eu_sel         ),
    .idu_fpu_ex1_func            ( {8'b0, div_op, sqrt_op}    ),
    .idu_fpu_ex1_gateclk_vld     ( fdsu_fpu_ex1_cmplt         ),
    .idu_fpu_ex1_rm              ( rnd_mode_q                 ),
    .idu_fpu_ex1_srcf0           ( operands_q[0][31:0]        ),
    .idu_fpu_ex1_srcf1           ( operands_q[1][31:0]        ),
    .idu_fpu_ex1_srcf2           ( '0                         ),
    .pad_yy_icg_scan_en          ( 1'b0                       )
  );

  assign ex2_inst_wb_vld_d = ctrl_fdsu_ex1_sel;
  `FF(ex2_inst_wb_vld_q, ex2_inst_wb_vld_d, '0)

  pa_fpu_frbus x_pa_fpu_frbus (
    .ctrl_frbus_ex2_wb_req     ( ex2_inst_wb & ex2_inst_wb_vld_q ),
    .dp_frbus_ex2_data         ( dp_frbus_ex2_data   ),
    .dp_frbus_ex2_fflags       ( dp_frbus_ex2_fflags ),
    .fdsu_frbus_data           ( fdsu_frbus_data     ),
    .fdsu_frbus_fflags         ( fdsu_frbus_fflags   ),
    .fdsu_frbus_wb_vld         ( fdsu_frbus_wb_vld   ),
    .fpu_idu_fwd_data          ( fpu_idu_fwd_data    ),  // output
    .fpu_idu_fwd_fflags        ( fpu_idu_fwd_fflags  ),  // output
    .fpu_idu_fwd_vld           ( fpu_idu_fwd_vld     )   // output
  );

  always_comb begin
    unit_result[31:0] = fpu_idu_fwd_data[31:0];
    unit_status[4:0]  = fpu_idu_fwd_fflags[4:0];
    unit_done         = fpu_idu_fwd_vld;
  end

  // The Hold register (load, no reset)
  `FFLNR(held_result_q, unit_result, hold_result, clk_i)
  `FFLNR(held_status_q, unit_status, hold_result, clk_i)

  // --------------
  // Output Select
  // --------------
  logic [WIDTH-1:0]   result_d;
  fpnew_pkg::status_t status_d;
  // Prioritize hold register data
  assign result_d = data_is_held ? held_result_q : unit_result;
  assign status_d = data_is_held ? held_status_q : unit_status;

  // ----------------
  // Output Pipeline
  // ----------------
  // Output pipeline signals, index i holds signal after i register stages
  logic               [0:NUM_OUT_REGS][WIDTH-1:0] out_pipe_result_q;
  fpnew_pkg::status_t [0:NUM_OUT_REGS]            out_pipe_status_q;
  TagType             [0:NUM_OUT_REGS]            out_pipe_tag_q;
  AuxType             [0:NUM_OUT_REGS]            out_pipe_aux_q;
  logic               [0:NUM_OUT_REGS]            out_pipe_mask_q;
  logic               [0:NUM_OUT_REGS]            out_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_OUT_REGS] out_pipe_ready;

  // Input stage: First element of pipeline is taken from inputs
  assign out_pipe_result_q[0] = result_d;
  assign out_pipe_status_q[0] = status_d;
  assign out_pipe_tag_q[0]    = result_tag_q;
  assign out_pipe_mask_q[0]   = result_mask_q;
  assign out_pipe_aux_q[0]    = result_aux_q;
  assign out_pipe_valid_q[0]  = out_valid;
  // Input stage: Propagate pipeline ready signal to inside pipe
  assign out_ready = out_pipe_ready[0];
  // Generate the register stages
  for (genvar i = 0; i < NUM_OUT_REGS; i++) begin : gen_output_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign out_pipe_ready[i] = out_pipe_ready[i+1] | ~out_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(out_pipe_valid_q[i+1], out_pipe_valid_q[i], out_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipleine ready and a valid data item is present
    assign reg_ena = (out_pipe_ready[i] & out_pipe_valid_q[i]) | reg_ena_i[NUM_INP_REGS + i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(out_pipe_result_q[i+1], out_pipe_result_q[i], reg_ena, '0)
    `FFL(out_pipe_status_q[i+1], out_pipe_status_q[i], reg_ena, '0)
    `FFL(out_pipe_tag_q[i+1],    out_pipe_tag_q[i],    reg_ena, TagType'('0))
    `FFL(out_pipe_mask_q[i+1],   out_pipe_mask_q[i],   reg_ena, '0)
    `FFL(out_pipe_aux_q[i+1],    out_pipe_aux_q[i],    reg_ena, AuxType'('0))
  end
  // Output stage: Ready travels backwards from output side, driven by downstream circuitry
  assign out_pipe_ready[NUM_OUT_REGS] = out_ready_i;
  // Output stage: assign module outputs
  assign result_o        = out_pipe_result_q[NUM_OUT_REGS];
  assign status_o        = out_pipe_status_q[NUM_OUT_REGS];
  assign extension_bit_o = 1'b1; // always NaN-Box result
  assign tag_o           = out_pipe_tag_q[NUM_OUT_REGS];
  assign mask_o          = out_pipe_mask_q[NUM_OUT_REGS];
  assign aux_o           = out_pipe_aux_q[NUM_OUT_REGS];
  assign out_valid_o     = out_pipe_valid_q[NUM_OUT_REGS];
  assign busy_o          = (| {inp_pipe_valid_q, unit_busy, out_pipe_valid_q});
endmodule
