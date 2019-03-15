// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright 2017 Embecosm Limited <www.embecosm.com>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module dp_ram
  #(
    parameter ADDR_WIDTH = 8,
    parameter RDATA_WIDTH = 32
  )(
    // Clock and Reset
    input logic                    clk,

    input logic                    en_a_i,
    input logic [ADDR_WIDTH-1:0]   addr_a_i,
    input logic [31:0]             wdata_a_i,
    output logic [RDATA_WIDTH-1:0] rdata_a_o,
    input logic                    we_a_i,
    input logic [3:0]              be_a_i,

    input logic                    en_b_i,
    input logic [ADDR_WIDTH-1:0]   addr_b_i,
    input logic [31:0]             wdata_b_i,
    output logic [31:0]            rdata_b_o,
    input logic                    we_b_i,
    input logic [3:0]              be_b_i
  );

  localparam bytes = 2**ADDR_WIDTH;

  logic [7:0] mem[bytes];
  logic [ADDR_WIDTH-1:0] addr_a_int;
  logic [ADDR_WIDTH-1:0] addr_b_int;

  // we always assume word based addressing
  always_comb addr_a_int = {addr_a_i[ADDR_WIDTH-1:2], 2'b0};
  always_comb addr_b_int = {addr_b_i[ADDR_WIDTH-1:2], 2'b0};

  always @(posedge clk)
  begin

      for (int i = 0; i < RDATA_WIDTH/4; i++) begin
          rdata_a_o[i*8+: 8] <= mem[addr_a_int +  i];
      end

    /* addr_b_i is the actual memory address referenced */

    if (en_b_i)
    begin
      /* handle writes */
      if (we_b_i)
      begin
        if (be_b_i[0]) mem[addr_b_int    ] <= wdata_b_i[ 0+:8];
        if (be_b_i[1]) mem[addr_b_int + 1] <= wdata_b_i[ 8+:8];
        if (be_b_i[2]) mem[addr_b_int + 2] <= wdata_b_i[16+:8];
        if (be_b_i[3]) mem[addr_b_int + 3] <= wdata_b_i[24+:8];
      end
      /* handle reads */
      else
      begin
        rdata_b_o[ 7: 0] <= mem[addr_b_int    ];
        rdata_b_o[15: 8] <= mem[addr_b_int + 1];
        rdata_b_o[23:16] <= mem[addr_b_int + 2];
        rdata_b_o[31:24] <= mem[addr_b_int + 3];
      end
    end
  end

  function [7:0] readByte;
    /* verilator public */
    input integer byte_addr;
    readByte = mem[byte_addr];
  endfunction

  task writeByte;
    /* verilator public */
    input integer byte_addr;
    input [7:0] val;
    mem[byte_addr] = val;
  endtask

endmodule
