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
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Load Store Unit                                            //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Load Store Unit, used to eliminate multiple access during  //
//                 processor stalls, and to align bytes and halfwords         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_load_store_unit #(
    parameter PULP_OBI = 0  // Legacy PULP OBI behavior
) (
    input logic clk,
    input logic rst_n,

    // output to data memory
    output logic data_req_o,
    input logic data_gnt_i,
    input logic data_rvalid_i,
    input  logic         data_err_i,           // External bus error (validity defined by data_rvalid_i) (not used yet)
    input logic data_err_pmp_i,  // PMP error (validity defined by data_gnt_i)

    output logic [31:0] data_addr_o,
    output logic        data_we_o,
    output logic [ 3:0] data_be_o,
    output logic [31:0] data_wdata_o,
    input  logic [31:0] data_rdata_i,

    // signals from ex stage
    input logic        data_we_ex_i,  // write enable                      -> from ex stage
    input logic [ 1:0] data_type_ex_i,  // Data type word, halfword, byte    -> from ex stage
    input logic [31:0] data_wdata_ex_i,  // data to write to memory           -> from ex stage
    input logic [ 1:0] data_reg_offset_ex_i,  // offset inside register for stores -> from ex stage
    input logic        data_load_event_ex_i,  // load event                        -> from ex stage
    input logic [ 1:0] data_sign_ext_ex_i,  // sign extension                    -> from ex stage

    output logic [31:0] data_rdata_ex_o,  // requested data                    -> to ex stage
    input  logic        data_req_ex_i,  // data request                      -> from ex stage
    input  logic [31:0] operand_a_ex_i,  // operand a from RF for address     -> from ex stage
    input  logic [31:0] operand_b_ex_i,  // operand b from RF for address     -> from ex stage
    input  logic        addr_useincr_ex_i,  // use a + b or just a for address   -> from ex stage

    input  logic data_misaligned_ex_i,  // misaligned access in last ld/st   -> from ID/EX pipeline
    output logic data_misaligned_o,  // misaligned access was detected    -> to controller

    input  logic [5:0] data_atop_ex_i,  // atomic instructions signal        -> from ex stage
    output logic [5:0] data_atop_o,  // atomic instruction signal         -> core output

    output logic p_elw_start_o,  // load event starts
    output logic p_elw_finish_o,  // load event finishes

    // stall signal
    output logic lsu_ready_ex_o,  // LSU ready for new data in EX stage
    output logic lsu_ready_wb_o,  // LSU ready for new data in WB stage

    output logic busy_o
);

  localparam DEPTH = 2;  // Maximum number of outstanding transactions

  // Transaction request (to cv32e40p_obi_interface)
  logic trans_valid;
  logic trans_ready;
  logic [31:0] trans_addr;
  logic trans_we;
  logic [3:0] trans_be;
  logic [31:0] trans_wdata;
  logic [5:0] trans_atop;

  // Transaction response interface (from cv32e40p_obi_interface)
  logic resp_valid;
  logic [31:0] resp_rdata;
  logic resp_err;  // Unused for now

  // Counter to count maximum number of outstanding transactions
  logic [1:0] cnt_q;  // Transaction counter
  logic [1:0] next_cnt;  // Next value for cnt_q
  logic         count_up;               // Increment outstanding transaction count by 1 (can happen at same time as count_down)
  logic         count_down;             // Decrement outstanding transaction count by 1 (can happen at same time as count_up)

  logic ctrl_update;  // Update load/store control info in WB stage

  logic [31:0] data_addr_int;

  // registers for data_rdata alignment and sign extension
  logic [1:0] data_type_q;
  logic [1:0] rdata_offset_q;
  logic [1:0] data_sign_ext_q;
  logic data_we_q;
  logic data_load_event_q;

  logic [1:0] wdata_offset;  // mux control for data to be written to memory

  logic [3:0] data_be;
  logic [31:0] data_wdata;

  logic misaligned_st;  // high if we are currently performing the second part of a misaligned store
  logic load_err_o, store_err_o;

  logic [31:0] rdata_q;

  ///////////////////////////////// BE generation ////////////////////////////////
  always_comb begin
    case (data_type_ex_i)  // Data type 00 Word, 01 Half word, 11,10 byte
      2'b00: begin  // Writing a word
        if (misaligned_st == 1'b0) begin  // non-misaligned case
          case (data_addr_int[1:0])
            2'b00:   data_be = 4'b1111;
            2'b01:   data_be = 4'b1110;
            2'b10:   data_be = 4'b1100;
            default: data_be = 4'b1000;
          endcase
          ;  // case (data_addr_int[1:0])
        end else begin  // misaligned case
          case (data_addr_int[1:0])
            2'b01:   data_be = 4'b0001;
            2'b10:   data_be = 4'b0011;
            2'b11:   data_be = 4'b0111;
            default: data_be = 4'b0000;  // this is not used, but included for completeness
          endcase
          ;  // case (data_addr_int[1:0])
        end
      end

      2'b01: begin  // Writing a half word
        if (misaligned_st == 1'b0) begin  // non-misaligned case
          case (data_addr_int[1:0])
            2'b00:   data_be = 4'b0011;
            2'b01:   data_be = 4'b0110;
            2'b10:   data_be = 4'b1100;
            default: data_be = 4'b1000;
          endcase
          ;  // case (data_addr_int[1:0])
        end else begin  // misaligned case
          data_be = 4'b0001;
        end
      end

      2'b10, 2'b11: begin  // Writing a byte
        case (data_addr_int[1:0])
          2'b00:   data_be = 4'b0001;
          2'b01:   data_be = 4'b0010;
          2'b10:   data_be = 4'b0100;
          default: data_be = 4'b1000;
        endcase
        ;  // case (data_addr_int[1:0])
      end
    endcase
    ;  // case (data_type_ex_i)
  end

  // prepare data to be written to the memory
  // we handle misaligned accesses, half word and byte accesses and
  // register offsets here
  assign wdata_offset = data_addr_int[1:0] - data_reg_offset_ex_i[1:0];
  always_comb begin
    case (wdata_offset)
      2'b00: data_wdata = data_wdata_ex_i[31:0];
      2'b01: data_wdata = {data_wdata_ex_i[23:0], data_wdata_ex_i[31:24]};
      2'b10: data_wdata = {data_wdata_ex_i[15:0], data_wdata_ex_i[31:16]};
      2'b11: data_wdata = {data_wdata_ex_i[7:0], data_wdata_ex_i[31:8]};
    endcase
    ;  // case (wdata_offset)
  end


  // FF for rdata alignment and sign-extension
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      data_type_q       <= '0;
      rdata_offset_q    <= '0;
      data_sign_ext_q   <= '0;
      data_we_q         <= 1'b0;
      data_load_event_q <= 1'b0;
    end
    else if (ctrl_update) // request was granted, we wait for rvalid and can continue to WB
    begin
      data_type_q       <= data_type_ex_i;
      rdata_offset_q    <= data_addr_int[1:0];
      data_sign_ext_q   <= data_sign_ext_ex_i;
      data_we_q         <= data_we_ex_i;
      data_load_event_q <= data_load_event_ex_i;
    end
  end

  // Load event starts when request is sent and finishes when (final) rvalid is received
  assign p_elw_start_o  = data_load_event_ex_i && data_req_o;
  assign p_elw_finish_o = data_load_event_q && data_rvalid_i && !data_misaligned_ex_i;

  ////////////////////////////////////////////////////////////////////////
  //  ____  _               _____      _                 _              //
  // / ___|(_) __ _ _ __   | ____|_  _| |_ ___ _ __  ___(_) ___  _ __   //
  // \___ \| |/ _` | '_ \  |  _| \ \/ / __/ _ \ '_ \/ __| |/ _ \| '_ \  //
  //  ___) | | (_| | | | | | |___ >  <| ||  __/ | | \__ \ | (_) | | | | //
  // |____/|_|\__, |_| |_| |_____/_/\_\\__\___|_| |_|___/_|\___/|_| |_| //
  //          |___/                                                     //
  ////////////////////////////////////////////////////////////////////////

  logic [31:0] data_rdata_ext;

  logic [31:0] rdata_w_ext;  // sign extension for words, actually only misaligned assembly
  logic [31:0] rdata_h_ext;  // sign extension for half words
  logic [31:0] rdata_b_ext;  // sign extension for bytes

  // take care of misaligned words
  always_comb begin
    case (rdata_offset_q)
      2'b00: rdata_w_ext = resp_rdata[31:0];
      2'b01: rdata_w_ext = {resp_rdata[7:0], rdata_q[31:8]};
      2'b10: rdata_w_ext = {resp_rdata[15:0], rdata_q[31:16]};
      2'b11: rdata_w_ext = {resp_rdata[23:0], rdata_q[31:24]};
    endcase
  end

  // sign extension for half words
  always_comb begin
    case (rdata_offset_q)
      2'b00: begin
        if (data_sign_ext_q == 2'b00) rdata_h_ext = {16'h0000, resp_rdata[15:0]};
        else if (data_sign_ext_q == 2'b10) rdata_h_ext = {16'hffff, resp_rdata[15:0]};
        else rdata_h_ext = {{16{resp_rdata[15]}}, resp_rdata[15:0]};
      end

      2'b01: begin
        if (data_sign_ext_q == 2'b00) rdata_h_ext = {16'h0000, resp_rdata[23:8]};
        else if (data_sign_ext_q == 2'b10) rdata_h_ext = {16'hffff, resp_rdata[23:8]};
        else rdata_h_ext = {{16{resp_rdata[23]}}, resp_rdata[23:8]};
      end

      2'b10: begin
        if (data_sign_ext_q == 2'b00) rdata_h_ext = {16'h0000, resp_rdata[31:16]};
        else if (data_sign_ext_q == 2'b10) rdata_h_ext = {16'hffff, resp_rdata[31:16]};
        else rdata_h_ext = {{16{resp_rdata[31]}}, resp_rdata[31:16]};
      end

      2'b11: begin
        if (data_sign_ext_q == 2'b00) rdata_h_ext = {16'h0000, resp_rdata[7:0], rdata_q[31:24]};
        else if (data_sign_ext_q == 2'b10)
          rdata_h_ext = {16'hffff, resp_rdata[7:0], rdata_q[31:24]};
        else rdata_h_ext = {{16{resp_rdata[7]}}, resp_rdata[7:0], rdata_q[31:24]};
      end
    endcase  // case (rdata_offset_q)
  end

  // sign extension for bytes
  always_comb begin
    case (rdata_offset_q)
      2'b00: begin
        if (data_sign_ext_q == 2'b00) rdata_b_ext = {24'h00_0000, resp_rdata[7:0]};
        else if (data_sign_ext_q == 2'b10) rdata_b_ext = {24'hff_ffff, resp_rdata[7:0]};
        else rdata_b_ext = {{24{resp_rdata[7]}}, resp_rdata[7:0]};
      end

      2'b01: begin
        if (data_sign_ext_q == 2'b00) rdata_b_ext = {24'h00_0000, resp_rdata[15:8]};
        else if (data_sign_ext_q == 2'b10) rdata_b_ext = {24'hff_ffff, resp_rdata[15:8]};
        else rdata_b_ext = {{24{resp_rdata[15]}}, resp_rdata[15:8]};
      end

      2'b10: begin
        if (data_sign_ext_q == 2'b00) rdata_b_ext = {24'h00_0000, resp_rdata[23:16]};
        else if (data_sign_ext_q == 2'b10) rdata_b_ext = {24'hff_ffff, resp_rdata[23:16]};
        else rdata_b_ext = {{24{resp_rdata[23]}}, resp_rdata[23:16]};
      end

      2'b11: begin
        if (data_sign_ext_q == 2'b00) rdata_b_ext = {24'h00_0000, resp_rdata[31:24]};
        else if (data_sign_ext_q == 2'b10) rdata_b_ext = {24'hff_ffff, resp_rdata[31:24]};
        else rdata_b_ext = {{24{resp_rdata[31]}}, resp_rdata[31:24]};
      end
    endcase  // case (rdata_offset_q)
  end

  // select word, half word or byte sign extended version
  always_comb begin
    case (data_type_q)
      2'b00:        data_rdata_ext = rdata_w_ext;
      2'b01:        data_rdata_ext = rdata_h_ext;
      2'b10, 2'b11: data_rdata_ext = rdata_b_ext;
    endcase  //~case(rdata_type_q)
  end

  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      rdata_q <= '0;
    end else begin
      if (resp_valid && (~data_we_q)) begin
        // if we have detected a misaligned access, and we are
        // currently doing the first part of this access, then
        // store the data coming from memory in rdata_q.
        // In all other cases, rdata_q gets the value that we are
        // writing to the register file
        if ((data_misaligned_ex_i == 1'b1) || (data_misaligned_o == 1'b1)) rdata_q <= resp_rdata;
        else rdata_q <= data_rdata_ext;
      end
    end
  end

  // output to register file
  assign data_rdata_ex_o = (resp_valid == 1'b1) ? data_rdata_ext : rdata_q;

  assign misaligned_st   = data_misaligned_ex_i;

  // Note: PMP is not fully supported at the moment (not even if USE_PMP = 1)
  assign load_err_o      = data_gnt_i && data_err_pmp_i && ~data_we_o;  // Not currently used
  assign store_err_o     = data_gnt_i && data_err_pmp_i && data_we_o;  // Not currently used


  // check for misaligned accesses that need a second memory access
  // If one is detected, this is signaled with data_misaligned_o to
  // the controller which selectively stalls the pipeline
  always_comb begin
    data_misaligned_o = 1'b0;

    if ((data_req_ex_i == 1'b1) && (data_misaligned_ex_i == 1'b0)) begin
      case (data_type_ex_i)
        2'b00: // word
        begin
          if (data_addr_int[1:0] != 2'b00) data_misaligned_o = 1'b1;
        end
        2'b01: // half word
        begin
          if (data_addr_int[1:0] == 2'b11) data_misaligned_o = 1'b1;
        end
      endcase  // case (data_type_ex_i)
    end
  end

  // generate address from operands
  assign data_addr_int = (addr_useincr_ex_i) ? (operand_a_ex_i + operand_b_ex_i) : operand_a_ex_i;

  // Busy if there are ongoing (or potentially outstanding) transfers
  assign busy_o = (cnt_q != 2'b00) || trans_valid;

  //////////////////////////////////////////////////////////////////////////////
  // Transaction request generation
  //
  // Assumes that corresponding response is at least 1 cycle after request
  //
  // - Only request transaction when EX stage requires data transfer (data_req_ex_i), and
  // - maximum number of outstanding transactions will not be exceeded (cnt_q < DEPTH)
  //////////////////////////////////////////////////////////////////////////////

  // For last phase of misaligned transfer the address needs to be word aligned (as LSB of data_be will be set)
  assign trans_addr = data_misaligned_ex_i ? {data_addr_int[31:2], 2'b00} : data_addr_int;
  assign trans_we = data_we_ex_i;
  assign trans_be = data_be;
  assign trans_wdata = data_wdata;
  assign trans_atop = data_atop_ex_i;

  // Transaction request generation
  generate
    if (PULP_OBI == 0) begin : gen_no_pulp_obi
      // OBI compatible (avoids combinatorial path from data_rvalid_i to data_req_o).
      // Multiple trans_* transactions can be issued (and accepted) before a response
      // (resp_*) is received.
      assign trans_valid = data_req_ex_i && (cnt_q < DEPTH);
    end else begin : gen_pulp_obi
      // Legacy PULP OBI behavior, i.e. only issue subsequent transaction if preceding transfer
      // is about to finish (re-introducing timing critical path from data_rvalid_i to data_req_o)
      assign trans_valid = (cnt_q == 2'b00) ? data_req_ex_i && (cnt_q < DEPTH) :
                                              data_req_ex_i && (cnt_q < DEPTH) && resp_valid;
    end
  endgenerate

  // LSU WB stage is ready if it is not being used (i.e. no outstanding transfers, cnt_q = 0),
  // or if it WB stage is being used and the awaited response arrives (resp_rvalid).
  assign lsu_ready_wb_o = (cnt_q == 2'b00) ? 1'b1 : resp_valid;

  // LSU EX stage readyness requires two criteria to be met:
  // 
  // - A data request (data_req_ex_i) has been forwarded/accepted (trans_valid && trans_ready)
  // - The LSU WB stage is available such that EX and WB can be updated in lock step
  //
  // Default (if there is not even a data request) LSU EX is signaled to be ready, else
  // if there are no outstanding transactions the EX stage is ready again once the transaction
  // request is accepted (at which time this load/store will move to the WB stage), else
  // in case there is already at least one outstanding transaction (so WB is full) the EX 
  // and WB stage can only signal readiness in lock step (so resp_valid is used as well).

  assign lsu_ready_ex_o = (data_req_ex_i == 1'b0) ? 1'b1 :
                          (cnt_q == 2'b00) ? (              trans_valid && trans_ready) : 
                          (cnt_q == 2'b01) ? (resp_valid && trans_valid && trans_ready) : 
                                              resp_valid;

  // Update signals for EX/WB registers (when EX has valid data itself and is ready for next)
  assign ctrl_update = lsu_ready_ex_o && data_req_ex_i;


  //////////////////////////////////////////////////////////////////////////////
  // Counter (cnt_q, next_cnt) to count number of outstanding OBI transactions 
  // (maximum = DEPTH)
  // 
  // Counter overflow is prevented by limiting the number of outstanding transactions
  // to DEPTH. Counter underflow is prevented by the assumption that resp_valid = 1 
  // will only occur in response to accepted transfer request (as per the OBI protocol).
  //////////////////////////////////////////////////////////////////////////////

  assign count_up = trans_valid && trans_ready;  // Increment upon accepted transfer request
  assign count_down = resp_valid;  // Decrement upon accepted transfer response

  always_comb begin
    unique case ({
      count_up, count_down
    })
      2'b00: begin
        next_cnt = cnt_q;
      end
      2'b01: begin
        next_cnt = cnt_q - 1'b1;
      end
      2'b10: begin
        next_cnt = cnt_q + 1'b1;
      end
      2'b11: begin
        next_cnt = cnt_q;
      end
    endcase
  end


  //////////////////////////////////////////////////////////////////////////////
  // Registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      cnt_q <= '0;
    end else begin
      cnt_q <= next_cnt;
    end
  end


  //////////////////////////////////////////////////////////////////////////////
  // OBI interface
  //////////////////////////////////////////////////////////////////////////////

  cv32e40p_obi_interface #(
      .TRANS_STABLE(1)
  ) data_obi_i (
      .clk  (clk),
      .rst_n(rst_n),

      .trans_valid_i(trans_valid),
      .trans_ready_o(trans_ready),
      .trans_addr_i (trans_addr),
      .trans_we_i   (trans_we),
      .trans_be_i   (trans_be),
      .trans_wdata_i(trans_wdata),
      .trans_atop_i (trans_atop),

      .resp_valid_o(resp_valid),
      .resp_rdata_o(resp_rdata),
      .resp_err_o  (resp_err),  // Unused for now

      .obi_req_o   (data_req_o),
      .obi_gnt_i   (data_gnt_i),
      .obi_addr_o  (data_addr_o),
      .obi_we_o    (data_we_o),
      .obi_be_o    (data_be_o),
      .obi_wdata_o (data_wdata_o),
      .obi_atop_o  (data_atop_o),  // Not (yet) defined in OBI 1.0 spec
      .obi_rdata_i (data_rdata_i),
      .obi_rvalid_i(data_rvalid_i),
      .obi_err_i   (data_err_i)  // External bus error (validity defined by obi_rvalid_i)
  );


  //////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////

`ifdef CV32E40P_ASSERT_ON

  // External data bus errors are not supported yet. PMP errors are not supported yet.
  // 
  // Note: Once PMP is re-introduced please consider to make data_err_pmp_i a 'data' signal
  // that is qualified with data_req_o && data_gnt_i (instead of suppressing data_gnt_i 
  // as is currently done. This will keep the data_req_o/data_gnt_i protocol intact.
  //
  // JUST RE-ENABLING the PMP VIA ITS USE_PMP LOCALPARAM WILL NOT WORK AS DATA_ERR_PMP_I 
  // NO LONGER FEEDS INTO LSU_READY_EX_O.

  property p_no_error;
    @(posedge clk) (1'b1) |-> ((data_err_i == 1'b0) && (data_err_pmp_i == 1'b0));
  endproperty

  a_no_error :
  assert property (p_no_error);

  // Check that outstanding transaction count will not overflow DEPTH
  property p_no_transaction_count_overflow_0;
    @(posedge clk) (1'b1) |-> (cnt_q <= DEPTH);
  endproperty

  a_no_transaction_count_overflow_0 :
  assert property (p_no_transaction_count_overflow_0);

  property p_no_transaction_count_overflow_1;
    @(posedge clk) (cnt_q == DEPTH) |-> (!count_up || count_down);
  endproperty

  a_no_transaction_count_overflow_1 :
  assert property (p_no_transaction_count_overflow_1);

  // Check that an rvalid only occurs when there are outstanding transaction(s)
  property p_no_spurious_rvalid;
    @(posedge clk) (data_rvalid_i == 1'b1) |-> (cnt_q > 0);
  endproperty

  a_no_spurious_rvalid :
  assert property (p_no_spurious_rvalid);

  // Check that the address/we/be/atop does not contain X when request is sent
  property p_address_phase_signals_defined;
    @(posedge clk) (data_req_o == 1'b1) |-> (!($isunknown(
        data_addr_o
    ) || $isunknown(
        data_we_o
    ) || $isunknown(
        data_be_o
    ) || $isunknown(
        data_atop_o
    )));
  endproperty

  a_address_phase_signals_defined :
  assert property (p_address_phase_signals_defined);

`endif

endmodule
