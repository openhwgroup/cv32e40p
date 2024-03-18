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

set synopsys_auto_setup true
set summary_log $::env(summary_log)
set top_module  $::env(top_module)
set version     $::env(version)
set pulp_cfg    $::env(pulp_cfg)
set fpu_cfg     $::env(fpu_cfg)
set zfinx_cfg   $::env(zfinx_cfg)

set top_impl_name cv32e40p_core_COREV_PULP${pulp_cfg}_FPU${fpu_cfg}_ZFINX${zfinx_cfg}

if {"$version" == "v1"} {
  set golden_parameter_list "PULP_XPULP = 0, FPU = 0, PULP_ZFINX = 0"
  set top_ref_name cv32e40p_core_PULP_XPULP0_FPU0_PULP_ZFINX0
} else {
  set golden_parameter_list "COREV_PULP = $pulp_cfg, FPU = $fpu_cfg, ZFINX = $zfinx_cfg"
  set top_ref_name $top_impl_name
}

read_sverilog -container r -libname WORK -12 -f golden.src
set_top r:/WORK/$top_module -parameter $golden_parameter_list

read_sverilog -container i -libname WORK -12 -f revised.src
set_top i:/WORK/$top_module -parameter "COREV_PULP = $pulp_cfg, FPU = $fpu_cfg, ZFINX = $zfinx_cfg"

match > $summary_log.match.rpt

if {"$top_module" == "cv32e40p_core"} {
    set_dont_verify_point -type port r:/WORK/$top_ref_name/apu_req_o
    set_dont_verify_point -type port r:/WORK/$top_ref_name/apu_operands_o*
    set_dont_verify_point -type port r:/WORK/$top_ref_name/apu_op_o*
    set_dont_verify_point -type port r:/WORK/$top_ref_name/apu_flags_o*
    set_dont_verify_point -type port i:/WORK/$top_impl_name/apu_req_o
    set_dont_verify_point -type port i:/WORK/$top_impl_name/apu_operands_o*
    set_dont_verify_point -type port i:/WORK/$top_impl_name/apu_op_o*
    set_dont_verify_point -type port i:/WORK/$top_impl_name/apu_flags_o*
}

verify > $summary_log

report_aborted_points > $summary_log.aborted_points.rpt
report_failing_points > $summary_log.failing_points.rpt

exit
