#################################################################################
# Synopsys Auto Setup Mode
#################################################################################

set synopsys_auto_setup true 

#################################################################################
# Analyze designs
#################################################################################

read_sverilog -container r -libname WORK -12 -f ../golden.src
set_top r:/WORK/cv32e40p_core 

read_sverilog -container i -libname WORK -12 -f ../revised.src
set_top i:/WORK/cv32e40p_core

#################################################################################
# Report design statistics, design read warning messages, and user specified setup
#################################################################################
# SOLVNET 
#set verification_clock_gate_edge_analysis true
set verification_clock_gate_reverse_gating true
report_setup_status

#################################################################################
# Match compare points and report unmatched points 
#################################################################################

match

report_unmatched_points > ./reports/unmatched_points.rpt

#################################################################################
# Verification ignoed points
#################################################################################

set_dont_verify_point -type port  i:WORK/cv32e40p_core/apu_req_o
set_dont_verify_point -type port  i:WORK/cv32e40p_core/apu_operands_o*
set_dont_verify_point -type port  i:WORK/cv32e40p_core/apu_op_o*
set_dont_verify_point -type port  i:WORK/cv32e40p_core/apu_flags_o*

report_dont_verify_points > ./reports/dont_verify_points.rpt

if { ![verify] }  {  
  save_session -replace ./reports/failing_session.fss
  report_failing_points > ./reports/report_failing_points.rpt
  report_aborted > ./reports/report_aborted.rpt
  # Use analyze_points to help determine the next step in resolving verification
  # issues. It runs heuristic analysis to determine if there are potential causes
  # other than logical differences for failing or hard verification points. 
  analyze_points -failing > ./reports/analyze_points.rpt
}

report_status > ./reports/result.rpt

exit
