
module insn_assert (
    input logic clk_i,
    input logic rst_ni,
    // Instruction memory interface
    input  logic        instr_req_o,
    input  logic        instr_gnt_i,
    input  logic        instr_rvalid_i
);

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

	assume_no_grnt_when_no_req: assume property(no_grnt_when_no_req);
	assume_no_rvalid_if_no_pending_req: assume property(no_rvalid_if_no_pending_req);

endmodule
