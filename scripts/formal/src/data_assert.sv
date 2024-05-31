// Copyright 2024 Dolphin Design
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License");
// you may not use this file except in compliance with the License, or,
// at your option, the Apache License version 2.0.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////////
//                                                                                //
// Contributors: Yoann Pruvost, Dolphin Design <yoann.pruvost@dolphin.fr>         //
//               Pascal Gouedo, Dolphin Design <pascal.gouedo@dolphin.fr>         //
//                                                                                //
// Description:  OBI protocol emulation for CV32E40P data interface               //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

module data_assert (
    input logic clk_i,
    input logic rst_ni,

    // Data memory interface
    input  logic        data_req_o,
    input  logic        data_gnt_i,
    input  logic        data_rvalid_i,
    input  logic        data_we_o,
    input  logic [ 3:0] data_be_o,
    input  logic [31:0] data_addr_o,
    input  logic [31:0] data_wdata_o,
    input  logic [31:0] data_rdata_i
);

	/*****************
	 * Helpers logic *
	 *****************/
	int s_outstanding_cnt;

	always_ff @(posedge clk_i or negedge rst_ni) begin
      if(!rst_ni) begin
        s_outstanding_cnt <= 0;
      end else if (data_req_o & data_gnt_i & data_rvalid_i) begin
        s_outstanding_cnt <= s_outstanding_cnt;
	  end else if (data_req_o & data_gnt_i) begin
          s_outstanding_cnt <= s_outstanding_cnt + 1;
	  end else if (data_rvalid_i) begin
          s_outstanding_cnt <= s_outstanding_cnt - 1;
	  end
    end

	/**********
	 * Assume *
	 **********/
	// Concerning lint_grnt
	property no_grnt_when_no_req;
		@(posedge clk_i) disable iff(!rst_ni)
			!data_req_o |-> !data_gnt_i;
	endproperty

	property no_rvalid_if_no_pending_req;
	    @(posedge clk_i) disable iff(!rst_ni)
			s_outstanding_cnt < 1 |-> !data_rvalid_i;
	endproperty

	assume_no_grnt_when_no_req: assume property(no_grnt_when_no_req);
	assume_no_rvalid_if_no_pending_req: assume property(no_rvalid_if_no_pending_req);
endmodule
