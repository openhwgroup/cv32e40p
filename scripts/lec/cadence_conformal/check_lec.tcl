// Copyright 2021 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

read_design -SV -replace -noelaborate -golden -File ../golden.src

elaborate_design -golden

read_design -SV -replace -noelaborate -revised -File ../revised.src

elaborate_design -revised

report_design_data > ./reports/report_design.log

add_ignored_outputs apu_req_o -Both
add_ignored_outputs apu_operands_o* -Both
add_ignored_outputs apu_op_o* -Both
add_ignored_outputs apu_flags_o* -Both

write_hier_compare_dofile hier_compare_r2r.do -constraint -replace

run_hier_compare hier_compare_r2r.do -ROOT_module cv32e40p_core cv32e40p_core

report_hier_compare_result -all -usage > ./reports/result.rpt
report_hier_compare_result -NONEQuivalent -usage > ./reports/result_noneq.rpt
report_verification -verbose -hier > ./reports/result_verfication.rpt

exit 0
