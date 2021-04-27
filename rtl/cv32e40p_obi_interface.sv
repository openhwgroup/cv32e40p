// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    OBI (Open Bus Interface)                                   //
// Project Name:   CV32E40P                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Open Bus Interface adapter. Translates transaction request //
//                 on the trans_* interface into an OBI A channel transfer.   //
//                 The OBI R channel transfer translated (i.e. passed on) as  //
//                 a transaction response on the resp_* interface.            //
//                                                                            //
//                 This adapter does not limit the number of outstanding      //
//                 OBI transactions in any way.                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_obi_interface #(
    parameter TRANS_STABLE =  0                   // Are trans_addr_i, trans_we_i, trans_be_i, trans_wdata_i, trans_atop_i signals stable during a non-accepted transaction?
) (
    input logic clk,
    input logic rst_n,

    // Transaction request interface
    input logic trans_valid_i,
    output logic trans_ready_o,
    input logic [31:0] trans_addr_i,
    input logic trans_we_i,
    input logic [3:0] trans_be_i,
    input logic [31:0] trans_wdata_i,
    input  logic  [5:0] trans_atop_i,             // Future proof addition (not part of OBI 1.0 spec; not used in CV32E40P)

    // Transaction response interface
    output logic resp_valid_o,  // Note: Consumer is assumed to be 'ready' whenever resp_valid_o = 1
    output logic [31:0] resp_rdata_o,
    output logic resp_err_o,

    // OBI interface
    output logic        obi_req_o,
    input  logic        obi_gnt_i,
    output logic [31:0] obi_addr_o,
    output logic        obi_we_o,
    output logic [ 3:0] obi_be_o,
    output logic [31:0] obi_wdata_o,
    output logic [ 5:0] obi_atop_o,
    input  logic [31:0] obi_rdata_i,
    input  logic        obi_rvalid_i,
    input  logic        obi_err_i
);

  enum logic {
    TRANSPARENT,
    REGISTERED
  }
      state_q, next_state;

  //////////////////////////////////////////////////////////////////////////////
  // OBI R Channel
  //////////////////////////////////////////////////////////////////////////////

  // The OBI R channel signals are passed on directly on the transaction response
  // interface (resp_*). It is assumed that the consumer of the transaction response
  // is always receptive when resp_valid_o = 1 (otherwise a response would get dropped)

  assign resp_valid_o = obi_rvalid_i;
  assign resp_rdata_o = obi_rdata_i;
  assign resp_err_o   = obi_err_i;


  //////////////////////////////////////////////////////////////////////////////
  // OBI A Channel
  //////////////////////////////////////////////////////////////////////////////

  generate
    if (TRANS_STABLE) begin : gen_trans_stable

      // If the incoming transaction itself is stable, then it satisfies the OBI protocol
      // and signals can be passed to/from OBI directly.
      assign obi_req_o     = trans_valid_i;
      assign obi_addr_o    = trans_addr_i;
      assign obi_we_o      = trans_we_i;
      assign obi_be_o      = trans_be_i;
      assign obi_wdata_o   = trans_wdata_i;
      assign obi_atop_o    = trans_atop_i;

      assign trans_ready_o = obi_gnt_i;

      // FSM not used
      assign state_q       = TRANSPARENT;
      assign next_state    = TRANSPARENT;
    end else begin : gen_no_trans_stable

      // OBI A channel registers (to keep A channel stable)
      logic [31:0] obi_addr_q;
      logic        obi_we_q;
      logic [ 3:0] obi_be_q;
      logic [31:0] obi_wdata_q;
      logic [ 5:0] obi_atop_q;

      // If the incoming transaction itself is not stable; use an FSM to make sure that
      // the OBI address phase signals are kept stable during non-granted requests.

      //////////////////////////////////////////////////////////////////////////////
      // OBI FSM
      //////////////////////////////////////////////////////////////////////////////

      // FSM (state_q, next_state) to control OBI A channel signals.

      always_comb begin
        next_state = state_q;

        case (state_q)

          // Default (transparent) state. Transaction requests are passed directly onto the OBI A channel.
          TRANSPARENT: begin
            if (obi_req_o && !obi_gnt_i) begin
              // OBI request not immediately granted. Move to REGISTERED state such that OBI address phase
              // signals can be kept stable while the transaction request (trans_*) can possibly change.
              next_state = REGISTERED;
            end
          end  // case: TRANSPARENT

          // Registered state. OBI address phase signals are kept stable (driven from registers).
          REGISTERED: begin
            if (obi_gnt_i) begin
              // Received grant. Move back to TRANSPARENT state such that next transaction request can be passed on.
              next_state = TRANSPARENT;
            end
          end  // case: REGISTERED

        endcase
      end

      always_comb begin
        if (state_q == TRANSPARENT) begin
          obi_req_o   = trans_valid_i;  // Do not limit number of outstanding transactions
          obi_addr_o  = trans_addr_i;
          obi_we_o    = trans_we_i;
          obi_be_o    = trans_be_i;
          obi_wdata_o = trans_wdata_i;
          obi_atop_o  = trans_atop_i;
        end else begin
          // state_q == REGISTERED
          obi_req_o   = 1'b1;  // Never retract request
          obi_addr_o  = obi_addr_q;
          obi_we_o    = obi_we_q;
          obi_be_o    = obi_be_q;
          obi_wdata_o = obi_wdata_q;
          obi_atop_o  = obi_atop_q;
        end
      end

      //////////////////////////////////////////////////////////////////////////////
      // Registers
      //////////////////////////////////////////////////////////////////////////////

      always_ff @(posedge clk, negedge rst_n) begin
        if (rst_n == 1'b0) begin
          state_q     <= TRANSPARENT;
          obi_addr_q  <= 32'b0;
          obi_we_q    <= 1'b0;
          obi_be_q    <= 4'b0;
          obi_wdata_q <= 32'b0;
          obi_atop_q  <= 6'b0;
        end else begin
          state_q <= next_state;
          if ((state_q == TRANSPARENT) && (next_state == REGISTERED)) begin
            // Keep OBI A channel signals stable throughout REGISTERED state
            obi_addr_q  <= obi_addr_o;
            obi_we_q    <= obi_we_o;
            obi_be_q    <= obi_be_o;
            obi_wdata_q <= obi_wdata_o;
            obi_atop_q  <= obi_atop_o;
          end
        end
      end

      // Always ready to accept a new transfer requests when previous A channel
      // transfer has been granted. Note that cv32e40p_obi_interface does not limit
      // the number of outstanding transactions in any way.
      assign trans_ready_o = (state_q == TRANSPARENT);

    end
  endgenerate

endmodule  // cv32e40p_obi_interface
