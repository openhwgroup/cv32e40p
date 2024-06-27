set top cv32e40p_wrapper
source ../../autocheck_common_rules.do
source ../../formal_lint_rules.do
autocheck report inconclusives
autocheck compile -work design_lib -d cv32e40p_wrapper -L design_lib -L work
autocheck verify -jobs 1
exit

