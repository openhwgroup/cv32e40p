/* Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * This code is under development and not yet released to the public.
 * Until it is released, the code is under the copyright of ETH Zurich and
 * the University of Bologna, and may contain confidential and/or unpublished
 * work. Any reuse/redistribution is strictly forbidden without written
 * permission from ETH Zurich.
 *
 * Bug fixes and contributions will eventually be released under the
 * SolderPad open hardware license in the context of the PULP platform
 * (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
 * University of Bologna.
 */

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
  // from id stage
  input  logic [31:0]              current_pc_i,

  // from hwloop_regs
  input  logic [N_REGS-1:0] [31:0] hwlp_start_addr_i,
  input  logic [N_REGS-1:0] [31:0] hwlp_end_addr_i,
  input  logic [N_REGS-1:0] [31:0] hwlp_counter_i,

  // to hwloop_regs
  output logic [N_REGS-1:0]        hwlp_dec_cnt_o,

  // from pipeline stages
  input  logic [N_REGS-1:0]        hwlp_dec_cnt_id_i,

  // to id stage
  output logic                     hwlp_jump_o,
  output logic [31:0]              hwlp_targ_addr_o
);


  logic [N_REGS-1:0] pc_is_end_addr;

  // end address detection
  integer j;


  // generate comparators. check for end address and the loop counter
  genvar i;
  generate
    for (i = 0; i < N_REGS; i++) begin
      always @(*)
      begin
        pc_is_end_addr[i] = 1'b0;

        if (current_pc_i == hwlp_end_addr_i[i]) begin
          if (hwlp_counter_i[i][31:2] != 30'h0) begin
            pc_is_end_addr[i] = 1'b1;
          end else begin
            // hwlp_counter_i[i][31:2] == 32'h0
            case (hwlp_counter_i[i][1:0])
              2'b11:        pc_is_end_addr[i] = 1'b1;
              2'b10:        pc_is_end_addr[i] = ~hwlp_dec_cnt_id_i[i]; // only when there is nothing in flight
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
      if (pc_is_end_addr[j]) begin
        hwlp_targ_addr_o  = hwlp_start_addr_i[j];
        hwlp_dec_cnt_o[j] = 1'b1;
        break;
      end
    end
  end

  // output signal for ID stage
  assign hwlp_jump_o = (|pc_is_end_addr);

endmodule
