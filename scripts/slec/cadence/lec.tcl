# Copyright 2024 OpenHW Group and Dolphin Design
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the “License”);
# you may not use this file except in compliance with the License, or,
# at your option, the Apache License version 2.0.
# You may obtain a copy of the License at
#
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an “AS IS” BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

set summary_log $::env(summary_log)
set top_module  $::env(top_module)
set version     $::env(version)
set pulp_cfg    $::env(pulp_cfg)
set fpu_cfg     $::env(fpu_cfg)
set zfinx_cfg   $::env(zfinx_cfg)
set latency_cfg $::env(latency_cfg)

if {"$version" == "v1"} {
  set golden_parameter_list "-parameter PULP_XPULP 0 -parameter FPU 0 -parameter PULP_ZFINX 0"
} else {
  set golden_parameter_list "-parameter COREV_PULP $pulp_cfg -parameter FPU $fpu_cfg -parameter ZFINX $zfinx_cfg -parameter FPU_ADDMUL_LAT $latency_cfg -parameter FPU_OTHERS_LAT $latency_cfg"
}

read_design -SV09 -replace -noelaborate -golden -File ./golden.src

elaborate_design -golden -root $top_module $golden_parameter_list

read_design -SV09 -replace -noelaborate -revised -File ./revised.src

elaborate_design -revised -root $top_module -parameter COREV_PULP $pulp_cfg -parameter FPU $fpu_cfg -parameter ZFINX $zfinx_cfg -parameter FPU_ADDMUL_LAT $latency_cfg -parameter FPU_OTHERS_LAT $latency_cfg

report_design_data

if {"$top_module" == "cv32e40p_core"} {
  add_ignored_outputs apu_req_o -Both
  add_ignored_outputs apu_operands_o* -Both
  add_ignored_outputs apu_op_o* -Both
  add_ignored_outputs apu_flags_o* -Both
  add_ignored_outputs apu_busy_o -Revised
}

write_hier_compare_dofile hier_compare_r2r.do -constraint -replace

run_hier_compare hier_compare_r2r.do -ROOT_module $top_module $top_module

report_hier_compare_result -all -usage > $summary_log
report_verification -verbose -hier >> $summary_log
report_hier_compare_result -NONEQuivalent -usage > $summary_log.noneq.rpt

exit 0
