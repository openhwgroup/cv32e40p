###################################################################

# Created by write_sdc on Mon Jun 9 16:58:54 2025

###################################################################
set sdc_version 2.1

set_units -time ns -resistance MOhm -capacitance fF -voltage V -current uA
set_max_fanout 100 [current_design]
create_clock [get_ports clk]  -period 8.5  -waveform {0 1}
set_clock_uncertainty 0.2  [get_clocks clk]
set_propagated_clock [get_clocks clk]
set_input_delay -clock clk  -max -rise 0.1  [get_ports rst_n]
set_input_delay -clock clk  -max -fall 0.1  [get_ports fetch_enable_i]
set_output_delay -clock clk  0.5  [get_ports ctrl_busy_o]
set_output_delay -clock clk  0.5  [get_ports is_decoding_o]
