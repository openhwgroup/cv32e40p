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
// Engineer:       Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
// Design Name:    Interrupt Controller                                       //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Interrupt Controller of the pipelined processor            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_int_controller import cv32e40p_pkg::*;
#(
  parameter PULP_SECURE = 0
)
(
  // irq_req for controller
  output logic        irq_req_ctrl_o,
  output logic        irq_sec_ctrl_o,
  output logic  [4:0] irq_id_ctrl_o,

  // external interrupt lines
  input  logic        irq_pending_i,            // Level-triggered interrupt inputs
  input  logic  [4:0] irq_pending_id_i,         // Interrupt id [0,1,....31]
  input  logic        irq_pending_sec_i,        // Interrupt secure bit from EU

  input  logic        m_ie_i,                   // Interrupt enable bit from CSR (M mode)
  input  logic        u_ie_i,                   // Interrupt enable bit from CSR (U mode)
  input  PrivLvl_t    current_priv_lvl_i
);

  logic irq_enable_ext;

if(PULP_SECURE)
  assign irq_enable_ext = ((u_ie_i || irq_pending_sec_i) && current_priv_lvl_i == PRIV_LVL_U) || (m_ie_i && current_priv_lvl_i == PRIV_LVL_M);
else
  assign irq_enable_ext = m_ie_i;

  assign irq_req_ctrl_o = irq_pending_i && irq_enable_ext;
  assign irq_id_ctrl_o  = irq_pending_id_i;
  assign irq_sec_ctrl_o = irq_pending_sec_i;

endmodule // cv32e40p_int_controller
