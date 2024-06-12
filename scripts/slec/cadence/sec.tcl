# Copyright 2021 OpenHW Group
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
set summary_log $::env(summary_log)
set top_module  $::env(top_module)
set report_dir  $::env(report_dir)

set_sec_disable_imp_assumption none

check_sec -setup -spec_top $top_module -imp_top $top_module \
        -spec_analyze  "-sv -f ./golden.src"\
        -imp_analyze "-sv -f ./revised.src"\
        -spec_elaborate_opts "-parameter COREV_PULP 1"\
        -imp_elaborate_opts  "-parameter COREV_PULP 1"\
        -auto_map_reset_x_values


clock clk_i
reset ~rst_ni

check_sec -map -auto

if {"$top_module" == "cv32e40p_core"} {
    check_sec -waive -waive_signals ex_stage_i.alu_i.ff_one_i.sel_nodes
    check_sec -waive -waive_signals cv32e40p_core_imp.ex_stage_i.alu_i.ff_one_i.sel_nodes

    check_sec -waive -waive_signals ex_stage_i.alu_i.ff_one_i.index_nodes
    check_sec -waive -waive_signals cv32e40p_core_imp.ex_stage_i.alu_i.ff_one_i.index_nodes
}

check_sec -prove

check_sec -signoff -get_valid_status -summary -file $summary_log

exit 0
