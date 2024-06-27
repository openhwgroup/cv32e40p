autocheck enable
autocheck disable -type ARITH_OVERFLOW_SUB
autocheck disable -type ARITH_OVERFLOW_VAL
autocheck disable -type CASE_DEFAULT
autocheck disable -type DECLARATION_UNUSED_UNDRIVEN
autocheck disable -type FUNCTION_INCOMPLETE_ASSIGN
autocheck disable -type INDEX_UNREACHABLE
autocheck disable -type INIT_X_OPTIMISM
autocheck disable -type INIT_X_PESSIMISM
autocheck disable -type INIT_X_UNRESOLVED
autocheck disable -type INIT_X_UNRESOLVED_MEM
autocheck disable -type REG_RACE
autocheck disable -type REG_STUCK_AT
configure message severity fatal -id elaboration-835
