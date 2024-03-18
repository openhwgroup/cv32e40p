// Copyright 2024 OpenHW Group and Dolphin Design
// Copyright 2017 ETH Zurich and University of Bologna.
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

// !!! cv32e40p_sim_clock_gate file is meant for simulation only !!!
// !!! It must not be used for ASIC synthesis                    !!!
// !!! It must not be used for FPGA synthesis                    !!!

module cv32e40p_clock_gate (
    input  logic clk_i,
    input  logic en_i,
    input  logic scan_cg_en_i,
    output logic clk_o
);

  logic clk_en;

  always_latch begin
    if (clk_i == 1'b0) clk_en <= en_i | scan_cg_en_i;
  end

  assign clk_o = clk_i & clk_en;

endmodule  // cv32e40p_clock_gate
