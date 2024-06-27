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
//                                                                                //
// Description:  OBI protocol emulation for CV32E40P instruction interface        //
//                                                                                //
////////////////////////////////////////////////////////////////////////////////////

module insn_assert (
    input logic clk_i,
    input logic rst_ni,
    // Instruction memory interface
    input  logic        instr_req_o,
    input  logic        instr_gnt_i,
    input  logic        instr_rvalid_i,
    input  logic [31:0] instr_addr_o,
    input  logic [31:0] instr_rdata_i
);

    import cv32e40p_pkg::*;
    import cv32e40p_tracer_pkg::*;

	/*****************
	 * Helpers logic *
	 *****************/
	int s_outstanding_cnt;

	always_ff @(posedge clk_i or negedge rst_ni) begin
      if(!rst_ni) begin
        s_outstanding_cnt <= 0;
      end else if (instr_req_o & instr_gnt_i & instr_rvalid_i) begin
        s_outstanding_cnt <= s_outstanding_cnt;
	  end else if (instr_req_o & instr_gnt_i) begin
          s_outstanding_cnt <= s_outstanding_cnt + 1;
	  end else if (instr_rvalid_i) begin
          s_outstanding_cnt <= s_outstanding_cnt - 1;
	  end
    end

	logic [31:0] s_prev_insn;
	always_ff @(posedge clk_i or negedge rst_ni) begin
      if(!rst_ni) begin
		s_prev_insn <= '0;
	  end else if (instr_rvalid_i) begin
		s_prev_insn <= instr_rdata_i;
	  end
	end

	/**********
	 * Assume *
	 **********/
	// Concerning lint_grnt
	property no_grnt_when_no_req;
		@(posedge clk_i) disable iff(!rst_ni)
			!instr_req_o |-> !instr_gnt_i;
	endproperty

	property no_rvalid_if_no_pending_req;
	    @(posedge clk_i) disable iff(!rst_ni)
			s_outstanding_cnt < 1 |-> !instr_rvalid_i;
	endproperty

	property no_compressed;
	    @(posedge clk_i) disable iff(!rst_ni)
	        instr_rdata_i[1:0] == 2'b11;
	endproperty

	property no_jump;
	    @(posedge clk_i) disable iff(!rst_ni)
		    (instr_rdata_i[6:0] != OPCODE_JAL) & (instr_rdata_i[6:0] != OPCODE_JALR);
	endproperty

	property no_branch;
	    @(posedge clk_i) disable iff(!rst_ni)
		    instr_rdata_i[6:0] != OPCODE_BRANCH;
	endproperty

	property no_custom0;
	@(posedge clk_i) disable iff(!rst_ni)
		    instr_rdata_i[6:0] != OPCODE_CUSTOM_0;
	endproperty

	property cvend0_only_after_cvstart0;
	    @(posedge clk_i) disable iff(!rst_ni)
		    (s_prev_insn != INSTR_CVSTARTI0) & (s_prev_insn != INSTR_CVSTARTI0) |-> (instr_rdata_i != INSTR_CVSENDI0) & (instr_rdata_i != INSTR_CVEND0);
	endproperty

	property cvcount0_only_after_cvend0;
	    @(posedge clk_i) disable iff(!rst_ni)
		    (s_prev_insn != INSTR_CVSENDI0) & (s_prev_insn != INSTR_CVEND0) |-> (instr_rdata_i != INSTR_CVCOUNTI0) & (instr_rdata_i != INSTR_CVCOUNT0);
	endproperty

	property no_cvsetup0;
	    @(posedge clk_i) disable iff(!rst_ni)
		    (instr_rdata_i != INSTR_CVSETUPI0) & (instr_rdata_i != INSTR_CVSETUP0);
	endproperty

	property no_cvstart0;
	    @(posedge clk_i) disable iff(!rst_ni)
		    (instr_rdata_i != INSTR_CVSTARTI0) & (instr_rdata_i != INSTR_CVSTART0);
	endproperty

	property cvend1_only_after_cvstart1;
	    @(posedge clk_i) disable iff(!rst_ni)
		    (s_prev_insn != INSTR_CVSTARTI1) & (s_prev_insn != INSTR_CVSTARTI1) |-> (instr_rdata_i != INSTR_CVSENDI1) & (instr_rdata_i != INSTR_CVEND1);
	endproperty

	property cvcount1_only_after_cvend1;
	    @(posedge clk_i) disable iff(!rst_ni)
		    (s_prev_insn != INSTR_CVSENDI1) & (s_prev_insn != INSTR_CVEND1) |-> (instr_rdata_i != INSTR_CVCOUNTI1) & (instr_rdata_i != INSTR_CVCOUNT1);
	endproperty

	property no_cvsetup1;
	    @(posedge clk_i) disable iff(!rst_ni)
		    (instr_rdata_i != INSTR_CVSETUPI1) & (instr_rdata_i != INSTR_CVSETUP1);
	endproperty

	property no_cvstart1;
	    @(posedge clk_i) disable iff(!rst_ni)
		    (instr_rdata_i != INSTR_CVSTARTI1) & (instr_rdata_i != INSTR_CVSTART1);
	endproperty

	property no_csr_write_to_hwloop;
	    @(posedge clk_i) disable iff(!rst_ni)
		    instr_rdata_i[6:0] == OPCODE_SYSTEM |-> (instr_rdata_i[31:20] != 12'hCC0) & (instr_rdata_i[31:20] != 12'hCC1) & (instr_rdata_i[31:20] != 12'hCC2) & (instr_rdata_i[31:20] != 12'hCC4) & (instr_rdata_i[31:20] != 12'hCC5) & (instr_rdata_i[31:20] != 12'hCC6);
	endproperty

	assume_no_grnt_when_no_req: assume property(no_grnt_when_no_req);
	assume_no_rvalid_if_no_pending_req: assume property(no_rvalid_if_no_pending_req);
	// assume_no_compressed: assume property(no_compressed);
	// assume_no_jump: assume property(no_jump);
	// assume_no_branch: assume property(no_branch);

	// assume_no_custom0: assume property(no_custom0);

	//hwloop 0 constraints
	// assume_cvend0_only_after_cvstart0: assume property(cvend0_only_after_cvstart0);
	// assume_cvcount0_only_after_cvend0: assume property(cvcount0_only_after_cvend0);
	// assume_no_cvsetup0: assume property(no_cvsetup0);
	// assume_no_cvstart0: assume property(no_cvstart0); //This one disables all hwloop0
	//hwloop 1 constraints
	// assume_cvend1_only_after_cvstart1: assume property(cvend1_only_after_cvstart1);
	// assume_cvcount1_only_after_cvend1: assume property(cvcount1_only_after_cvend1);
	// assume_no_cvsetup1: assume property(no_cvsetup1);
	// assume_no_cvstart1: assume property(no_cvstart1); //This one disables all hwloop1

	assume_no_csr_write_to_hwloop: assume property(no_csr_write_to_hwloop);

endmodule