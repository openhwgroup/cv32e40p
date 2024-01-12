set synopsys_auto_setup true
set summary_log $::env(summary_log)
set top_module  $::env(top_module)

read_sverilog -container r -libname WORK -12 -f golden.src
set_top r:/WORK/$top_module

read_sverilog -container i -libname WORK -12 -f revised.src
set_top i:/WORK/$top_module

match > ./reports/match.rpt

if {"$top_module" == "cv32e40p_core"} {
    set_dont_verify_point -type port i:WORK/cv32e40p_core/apu_req_o
    set_dont_verify_point -type port i:WORK/cv32e40p_core/apu_operands_o*
    set_dont_verify_point -type port i:WORK/cv32e40p_core/apu_op_o*
    set_dont_verify_point -type port i:WORK/cv32e40p_core/apu_flags_o*
}

verify > $summary_log

report_aborted_points > $summary_log.aborted_points.rpt
report_failing_points > $summary_log.failing_points.rpt
analyze_points -failing >> $summary_log

exit
