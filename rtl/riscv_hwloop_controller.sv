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
// Engineer:       Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    hwloop controller                                          //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Hardware loop controller unit. This unit is responsible to //
//                 handle hardware loops. Tasks are:                          //
//                 a) compare PC to all stored end addresses                  //
//                 b) jump to the right start address if counter =/ 0         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module riscv_hwloop_controller
#(
  parameter N_REGS = 2
)
(

  input  logic                     clk,
  input  logic                     rst_n,

  input  logic                     id_valid_i,
  input  logic                     instr_valid_i,
  input  logic [31:0]              current_pc_i,

  // from hwloop_regs
  input  logic [N_REGS-1:0] [31:0] hwlp_start_addr_i,
  input  logic [N_REGS-1:0] [31:0] hwlp_end_addr_i,
  input  logic [N_REGS-1:0] [31:0] hwlp_counter_i,

  // to hwloop_regs
  output logic [N_REGS-1:0]        hwlp_dec_cnt_o,

  // to id stage
  output logic                     hwlp_jump_o,
  output logic [31:0]              hwlp_targ_addr_o,

  output logic                     hwlp_jump_pc_o,
  output logic [31:0]              hwlp_targ_addr_pc_o
);


  logic [N_REGS-1:0] pc_is_end_addr, pc_is_end_addr_pc_q, counter_not_zero;
  logic [31:0]       hwlp_targ_addr_q;
  // end address detection
  integer j;

  assign hwlp_targ_addr_pc_o = hwlp_targ_addr_q;

  // generate comparators. check for end address and the loop counter
  genvar i;
  generate
    for (i = 0; i < N_REGS; i++) begin
      always @(*)
      begin
        pc_is_end_addr[i]    = 1'b0;
        counter_not_zero[i]  = hwlp_counter_i[i][31:2] != 30'h0;

        if ((current_pc_i + 4 == hwlp_end_addr_i[i]) && id_valid_i && instr_valid_i) begin
          if (counter_not_zero[i]) begin
            pc_is_end_addr[i] = 1'b1;
          end else begin
            // hwlp_counter_i[i][31:2] == 32'h0
            case (hwlp_counter_i[i][1:0])
              2'b11, 2'b10: pc_is_end_addr[i] = 1'b1;
              2'b01, 2'b00: pc_is_end_addr[i] = 1'b0;
            endcase
          end
        end

      end
    end
  endgenerate

  // select corresponding start address and decrement counter
  always_comb
  begin
    hwlp_targ_addr_o = '0;
    hwlp_dec_cnt_o   = '0;

    for (j = 0; j < N_REGS; j++) begin
      if (pc_is_end_addr[j] && id_valid_i) begin
        hwlp_targ_addr_o  = hwlp_start_addr_i[j];
        hwlp_dec_cnt_o[j] = 1'b1;
        break;
      end
    end
  end

  // output signal for ID stage
  assign hwlp_jump_o      = (|pc_is_end_addr);
  assign hwlp_jump_pc_o   = (|pc_is_end_addr_pc_q);

  always_ff @(posedge clk or negedge rst_n) begin
    if(~rst_n) begin
       pc_is_end_addr_pc_q <= '0;
       hwlp_targ_addr_q    <= '0;
    end else begin
      // Inf id_valid_i is low, do not updated the hwloop_target_address.
      // Otherwise the Hwloop Branch result in a lost jump inside the prefetch buffer
      if(instr_valid_i & id_valid_i) begin
          hwlp_targ_addr_q    <= hwlp_targ_addr_o;
          pc_is_end_addr_pc_q <= pc_is_end_addr;
      end
    end
  end


endmodule
