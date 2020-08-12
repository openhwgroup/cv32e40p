
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
// Engineer:       Francesco Conti - f.conti@unibo.it                         //
//                                                                            //
// Additional contributions by:                                               //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Noam Gallmann    - gnoam@student.ethz.ch                   //
//                                                                            //
// Design Name:    RISC-V register file                                       //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Register file with 31x 32 bit wide registers. Register 0   //
//                 is fixed to 0. This register file is optimized for FPGAs   //
//                 featuring distributed RAM-enabled logic cells.             //
//                 Also supports the fp-register file now if FPU=1            //
//                 If PULP_ZFINX is 1, floating point operations take values  //
//                 from the X register file                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_register_file
#(
    parameter ADDR_WIDTH    = 5,
    parameter DATA_WIDTH    = 32,
    parameter FPU           = 0,
    parameter PULP_ZFINX    = 0
)
(
    // Clock and Reset
    input  logic         clk,
    input  logic         rst_n,

    input  logic         scan_cg_en_i,

    //Read port R1
    input  logic [ADDR_WIDTH-1:0]  raddr_a_i,
    output logic [DATA_WIDTH-1:0]  rdata_a_o,

    //Read port R2
    input  logic [ADDR_WIDTH-1:0]  raddr_b_i,
    output logic [DATA_WIDTH-1:0]  rdata_b_o,

    //Read port R3
    input  logic [ADDR_WIDTH-1:0]  raddr_c_i,
    output logic [DATA_WIDTH-1:0]  rdata_c_o,

    // Write port W1
    input logic [ADDR_WIDTH-1:0]   waddr_a_i,
    input logic [DATA_WIDTH-1:0]   wdata_a_i,
    input logic                    we_a_i,

    // Write port W2
    input logic [ADDR_WIDTH-1:0]   waddr_b_i,
    input logic [DATA_WIDTH-1:0]   wdata_b_i,
    input logic                    we_b_i
);

  // The register values are stored in two separate RAM blocks each featuring 1 sync-write and
  // 3 async-read ports. A set of 1-bit flip-flops keeps track of which RAM block contains the valid
  // entry for each register.
  // The integer register file occupies adresses 0-31. If enabled, the floating-point registers are
  // located at addresses 32-63.

  // number of integer registers
  localparam    NUM_WORDS     = 2**(ADDR_WIDTH-1);
  // number of floating point registers
  localparam    NUM_FP_WORDS  = 2**(ADDR_WIDTH-1);
  localparam    NUM_TOT_WORDS = FPU ? ( PULP_ZFINX ? NUM_WORDS : NUM_WORDS + NUM_FP_WORDS ) : NUM_WORDS;

  // integer and floating-point register file
  // distributed RAM blocks
  logic [DATA_WIDTH-1:0]                    mem_a [NUM_TOT_WORDS];
  logic [DATA_WIDTH-1:0]                    mem_b [NUM_TOT_WORDS];

  // distributed RAM block selectors
  logic [NUM_TOT_WORDS-1:0]                 mem_block_sel;
  logic [NUM_TOT_WORDS-1:0]                 mem_block_sel_q;

  // write enable signals for all registers
  logic [NUM_TOT_WORDS-1:0]                 we_a_dec;
  logic [NUM_TOT_WORDS-1:0]                 we_b_dec;

  //-----------------------------------------------------------------------------
  //-- READ : Read address decoder RAD
  //-----------------------------------------------------------------------------

  // Read from the block corresponding to the write port that last wrote to the corresponding
  // address.
  if (FPU == 1 && PULP_ZFINX == 0) begin
    assign rdata_a_o = (raddr_a_i == '0) ? '0 :
       mem_block_sel_q[raddr_a_i[5:0]] ? mem_b[raddr_a_i[5:0]] : mem_a[raddr_a_i[5:0]];
    assign rdata_b_o = (raddr_b_i == '0) ? '0 :
       mem_block_sel_q[raddr_b_i[5:0]] ? mem_b[raddr_b_i[5:0]] : mem_a[raddr_b_i[5:0]];
    assign rdata_c_o = (raddr_c_i == '0) ? '0 :
       mem_block_sel_q[raddr_c_i[5:0]] ? mem_b[raddr_c_i[5:0]] : mem_a[raddr_c_i[5:0]];
  end else begin
    assign rdata_a_o = (raddr_a_i == '0) ? '0 :
       mem_block_sel_q[raddr_a_i[4:0]] ? mem_b[raddr_a_i[4:0]] : mem_a[raddr_a_i[4:0]];
    assign rdata_b_o = (raddr_b_i == '0) ? '0 :
       mem_block_sel_q[raddr_b_i[4:0]] ? mem_b[raddr_b_i[4:0]] : mem_a[raddr_b_i[4:0]];
    assign rdata_c_o = (raddr_c_i == '0) ? '0 :
       mem_block_sel_q[raddr_c_i[4:0]] ? mem_b[raddr_c_i[4:0]] : mem_a[raddr_c_i[4:0]];
  end

  //-----------------------------------------------------------------------------
  //-- WRITE : Write Address Decoder (WAD)
  //-----------------------------------------------------------------------------

  always_comb begin : we_a_decoder
    for (int i = 0; i < NUM_TOT_WORDS; i++) begin
      if (waddr_a_i == i) begin
        we_a_dec[i] = we_a_i;
      end else begin
        we_a_dec[i] = 1'b0;
      end
    end
  end

  always_comb begin : we_b_decoder
    for (int i=0; i<NUM_TOT_WORDS; i++) begin
      if (waddr_b_i == i) begin
        we_b_dec[i] = we_b_i;
      end else begin
        we_b_dec[i] = 1'b0;
      end
    end
  end

  // update block selector:
  // signal mem_block_sel records where the current valid value is stored.
  // if port a and b try to write to the same address simultaneously, write port b has priority.
  always_comb begin
    mem_block_sel[0] = '0;
    for (int i = 1; i<NUM_TOT_WORDS; i++) begin
      if (we_b_dec[i] == 1'b1) begin
        mem_block_sel[i] = 1'b1;
      end else if (we_a_dec[i] == 1'b1) begin
        mem_block_sel[i] = 1'b0;
      end else begin
        mem_block_sel[i] = mem_block_sel_q[i];
      end
    end
  end

  // block selector flops
  always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      mem_block_sel_q <= '0;
    end else begin
      mem_block_sel_q <= mem_block_sel;
    end
  end

  always_ff @(posedge clk) begin : regs_a
    if(we_a_i) begin
      mem_a[waddr_a_i] <= wdata_a_i;
    end
  end

  always_ff @(posedge clk) begin : regs_b
    if(we_b_i) begin
      mem_b[waddr_b_i] <= wdata_b_i;
    end
  end

endmodule
