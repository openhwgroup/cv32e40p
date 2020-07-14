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
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Fetch Fifo for 32 bit memory interface                     //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Buffer to store instructions.                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// input port: send address one cycle before the data
// branch_i clears the FIFO for the following cycle. branch_addr_i can be sent in
// this cycle already

module cv32e40p_fetch_fifo
#(
  parameter DEPTH = 4                           // Prefetch FIFO Depth
)(
    input  logic        clk,
    input  logic        rst_n,

    // control signals
    input  logic        branch_i,               // Taken branch. Clears the contents of the fifo
    input  logic [31:0] branch_addr_i,          // Branch target address (only valid when branch_i == 1)

    // input port
    input  logic [31:0] in_rdata_i,             // Instruction(s) to be written to the FIFO
    input  logic        in_valid_i,             // Validity of in_rdata_i (only allowed when FIFO is not full)
    output logic  [2:0] in_cnt_o,               // Number of items in the FIFO (set to 0 combinatorially upon a branch)

    // output port
    output logic        out_valid_o,            // Validity of out_rdata_o
    input  logic        out_ready_i,
    output logic [31:0] out_rdata_o,            // Instruction to IF stage
    output logic [31:0] out_addr_o              // Address (PC) associated with out_rdata_o
  );

  // index 0 is used for output
  logic [0:DEPTH-1] [31:0]  rdata_n,   rdata_int,   rdata_q;
  logic [0:DEPTH-1]         valid_n,   valid_int,   valid_q;

  logic             [31:0]  addr_n, addr_q, addr_incr;
  logic             [31:0]  rdata, rdata_unaligned;
  logic                     valid, valid_unaligned;

  logic                     aligned_is_compressed, unaligned_is_compressed;

  //////////////////////////////////////////////////////////////////////////////
  // output port
  //////////////////////////////////////////////////////////////////////////////

  assign rdata = (valid_q[0]) ? rdata_q[0] : in_rdata_i;
  assign valid = valid_q[0] || in_valid_i;

  assign rdata_unaligned = (valid_q[1]) ? {rdata_q[1][15:0], rdata[31:16]} : {in_rdata_i[15:0], rdata[31:16]};
  // it is implied that rdata_valid_q[0] is set
  assign valid_unaligned = (valid_q[1] || (valid_q[0] && in_valid_i));

  // unaligned_is_compressed and aligned_is_compressed are only defined when valid = 1 (which implies that out_valid_o will be 1)
  assign unaligned_is_compressed = rdata[17:16] != 2'b11;
  assign aligned_is_compressed   = rdata[1:0] != 2'b11;

  //////////////////////////////////////////////////////////////////////////////
  // instruction aligner (if unaligned)
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    if (out_addr_o[1]) begin
      // unaligned case
      out_rdata_o = rdata_unaligned;

      if (!valid) begin
        out_valid_o = valid;
      end else if (unaligned_is_compressed) begin
        out_valid_o = valid;
      end else begin
        out_valid_o = valid_unaligned;
      end
    end else begin
      // aligned case
      out_rdata_o = rdata;
      out_valid_o = valid;
    end
  end

  assign out_addr_o = addr_q;


  //////////////////////////////////////////////////////////////////////////////
  // input port
  //////////////////////////////////////////////////////////////////////////////

  // Indicate FIFO fill count. On a branch (branch_i) the FIFO will be cleared
  // on the next clock edge. Ahead of that the FIFO is indicated to be empty 
  // so that a new transaction request in response to a branch are always
  // requested as soon as possible.

  assign in_cnt_o = branch_i ? 3'b000 :                 // FIFO will be cleared on next clock edge (and branch target instruction cannot arrive earlier)
                    valid_q[3] ? 3'b100 :
                    valid_q[2] ? 3'b011 :
                    valid_q[1] ? 3'b010 :
                    valid_q[0] ? 3'b001 : 3'b000;


  //////////////////////////////////////////////////////////////////////////////
  // FIFO management
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    rdata_int   = rdata_q;
    valid_int   = valid_q;

    if (in_valid_i) begin
      for(int j = 0; j < DEPTH; j++) begin
        if (~valid_q[j]) begin
          rdata_int[j] = in_rdata_i;
          valid_int[j] = 1'b1;

          break;
        end
      end
    end
  end

  assign addr_incr = {addr_q[31:2], 2'b00} + 32'h4;

  // move everything by one step
  always_comb
  begin
    addr_n     = addr_q;
    rdata_n    = rdata_int;
    valid_n    = valid_int;

    if (out_ready_i && out_valid_o) begin
      if (addr_q[1]) begin
        // unaligned case
        if (unaligned_is_compressed) begin
          addr_n = {addr_incr[31:2], 2'b00};
        end else begin
          addr_n = {addr_incr[31:2], 2'b10};
        end
        for (int i = 0; i < DEPTH - 1; i++)
        begin
          rdata_n[i] = rdata_int[i + 1];
        end
        valid_n = {valid_int[1:DEPTH-1], 1'b0};
      end else begin
        // aligned case
        if (aligned_is_compressed) begin
          // just increase address, do not move to next entry in FIFO
          addr_n = {addr_q[31:2], 2'b10};
        end else begin
          // move to next entry in FIFO
          addr_n = {addr_incr[31:2], 2'b00};
          for (int i = 0; i < DEPTH - 1; i++)
          begin
            rdata_n[i] = rdata_int[i + 1];
          end
          valid_n = {valid_int[1:DEPTH-1], 1'b0};
        end
      end
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      addr_q    <= '0;
      rdata_q   <= '{default: '0};
      valid_q   <= '0;
    end
    else
    begin
      // on a clear signal from outside we invalidate the content of the FIFO
      // completely and start from an empty state
      if (branch_i) begin
        valid_q <= '0;
        addr_q  <= branch_addr_i;       // Branch target address will correspond to first instruction received after this. 
      end else begin
        addr_q  <= addr_n;
        rdata_q <= rdata_n;
        valid_q <= valid_n;
      end
    end
  end

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifdef CV32E40P_ASSERT_ON

  // Check for FIFO overflows
  assert property (
     @(posedge clk) (in_valid_i) |-> (valid_q[DEPTH-1] == 1'b0) );

  // Check that FIFO is cleared the cycle after a branch
  assert property (
     @(posedge clk) (branch_i) |=> (valid_q == 'b0) );

  // Check that FIFO is signaled empty the cycle during a branch
  assert property (
     @(posedge clk) (branch_i) |-> (in_cnt_o == 'b0) );

`endif

endmodule
