# define all clocks
netlist clock clk_i -period 100 -waveform 0 50

# define all reset
netlist reset rst_ni -active_low -async

# define clock domain for reset
netlist port domain rst_ni -clock clk_i

# define special case
netlist constant scan_cg_en_i 1'b0
netlist constant pulp_clock_en_i 1'b0

# disable rules
autocheck disable -type FSM_DEADLOCK_STATE FSM_LOCKOUT_STATE

