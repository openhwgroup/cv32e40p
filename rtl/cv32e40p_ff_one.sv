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
// Engineer:       Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    cv32e40p_ff_one                                               //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Find First One                                             //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_ff_one #(
    parameter LEN = 32
) (
    input logic [LEN-1:0] in_i,

    output logic [$clog2(LEN)-1:0] first_one_o,
    output logic                   no_ones_o
);

  localparam NUM_LEVELS = $clog2(LEN);

  logic [          LEN-1:0][NUM_LEVELS-1:0] index_lut;
  logic [2**NUM_LEVELS-1:0]                 sel_nodes;
  logic [2**NUM_LEVELS-1:0][NUM_LEVELS-1:0] index_nodes;


  //////////////////////////////////////////////////////////////////////////////
  // generate tree structure
  //////////////////////////////////////////////////////////////////////////////

  generate
    genvar j;
    for (j = 0; j < LEN; j++) begin : gen_index_lut
      assign index_lut[j] = $unsigned(j);
    end
  endgenerate

  generate
    genvar k;
    genvar l;
    genvar level;

    assign sel_nodes[2**NUM_LEVELS-1] = 1'b0;

    for (level = 0; level < NUM_LEVELS; level++) begin : gen_tree
      //------------------------------------------------------------
      if (level < NUM_LEVELS - 1) begin : gen_non_root_level
        for (l = 0; l < 2 ** level; l++) begin : gen_node
          assign sel_nodes[2**level-1+l]   = sel_nodes[2**(level+1)-1+l*2] | sel_nodes[2**(level+1)-1+l*2+1];
          assign index_nodes[2**level-1+l] = (sel_nodes[2**(level+1)-1+l*2] == 1'b1) ?
                                           index_nodes[2**(level+1)-1+l*2] : index_nodes[2**(level+1)-1+l*2+1];
        end
      end
      //------------------------------------------------------------
      if (level == NUM_LEVELS - 1) begin : gen_root_level
        for (k = 0; k < 2 ** level; k++) begin : gen_node
          // if two successive indices are still in the vector...
          if (k * 2 < LEN - 1) begin : gen_two
            assign sel_nodes[2**level-1+k] = in_i[k*2] | in_i[k*2+1];
            assign index_nodes[2**level-1+k] = (in_i[k*2] == 1'b1) ? index_lut[k*2] : index_lut[k*2+1];
          end
          // if only the first index is still in the vector...
          if (k * 2 == LEN - 1) begin : gen_one
            assign sel_nodes[2**level-1+k]   = in_i[k*2];
            assign index_nodes[2**level-1+k] = index_lut[k*2];
          end
          // if index is out of range
          if (k * 2 > LEN - 1) begin : gen_out_of_range
            assign sel_nodes[2**level-1+k]   = 1'b0;
            assign index_nodes[2**level-1+k] = '0;
          end
        end
      end
      //------------------------------------------------------------
    end
  endgenerate

  //////////////////////////////////////////////////////////////////////////////
  // connect output
  //////////////////////////////////////////////////////////////////////////////

  assign first_one_o = index_nodes[0];
  assign no_ones_o   = ~sel_nodes[0];

endmodule
