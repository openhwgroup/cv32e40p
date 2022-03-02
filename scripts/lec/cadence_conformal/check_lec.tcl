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

read design -SV -replace -golden -noelaborate $cnf_golden_rtl

elaborate design -golden

read design -SV -replace -revised -noelaborate $cnf_revised_rtl

elaborate design -revised

report design data > ./lec_reports/report_design.log

add ignored outputs apu_req_o -Both
add ignored outputs apu_operands_o* -Both
add ignored outputs apu_op_o* -Both
add ignored outputs apu_flags_o* -Both

write hier_compare dofile hier_compare_r2r.do -constraint -replace

run hier_compare hier_compare_r2r.do -ROOT_module cv32e40p_core cv32e40p_core

report hier result -all -usage > ./lec_reports/result.rpt
report hier result -noneq -usage > ./lec_reports/result_noneq.rpt
report verification -verbose -hier > ./lec_reports/result_verfication.rpt

exit -f
