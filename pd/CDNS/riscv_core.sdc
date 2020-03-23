##################################################################
##                                                      	##
##                      BTA Design Services             	##
##      Author  :       Ludmila Rubin                   	##
##      Email   :       lrubin@btadesignservices.com    	##
##	Date	:	Mar 19, 2020				##
##      Abstract:       Example of SDC timing constraints 	##
##			for riscv_core design			##
##                                                      	##
##################################################################



set PERIOD	3.125 ;# 320MHz

set WAVEFORM 	[list 0 [expr $PERIOD / 2]]
set INP_DLY	[expr $PERIOD * 0.7 ]		;# 30% of the clock for block level, 70% is reserved for the top
set OUT_DLY	[expr $PERIOD * 0.7 ]		;# 30% of the clock for block level, 70% is reserved for the top

## Create the clocks
echo "Creating the clock clk_i"
create_clock -name clk_i -period $PERIOD -waveform $WAVEFORM [get_ports clk_i]

## Set IO delays
echo "Setting input and output delays"
set_input_delay  -add_delay $INP_DLY -max -clock clk_i [remove_from_collection [all_inputs]  [get_ports {clk_i}]]
set_output_delay -add_delay $OUT_DLY -max -clock clk_i [remove_from_collection [all_outputs] [get_ports {clk_i}]]


## Exceptions (false paths, multicycle etc.)
echo "Setting the exceptions"
set_false_path -from [get_ports "debug_req_i"] -to [get_ports "instr_addr_o*"]
set_false_path -from [get_ports "debug_req_i"] -to [get_ports "instr_req_o"]

### reg2out ####
set_multicycle_path 2 -setup -from [get_clocks clk_i] -to [get_ports "instr_addr_o*"]
set_multicycle_path 2 -setup -from [get_clocks clk_i] -to [get_ports "data_addr_o*"]
set_multicycle_path 2 -setup -from [get_clocks clk_i] -to [get_ports "instr_req_o"]
set_multicycle_path 2 -setup -from [get_clocks clk_i] -to [get_ports "data_wdata_o*"]
set_multicycle_path 2 -setup -from [get_clocks clk_i] -to [get_ports "data_be_o*"]
set_multicycle_path 2 -setup -from [get_clocks clk_i] -to [get_ports "core_busy_o"]
set_multicycle_path 2 -setup -from [get_clocks clk_i] -to [get_ports "data_req_o"]
set_multicycle_path 2 -setup -from [get_clocks clk_i] -to [get_ports "irq_ack_o"]

### in2reg ###
set_multicycle_path 2 -setup -from [get_ports "data_rdata_i*"]  -to [get_clocks clk_i]
set_multicycle_path 2 -setup -from [get_ports "instr_rvalid_i"] -to [get_clocks clk_i]



### in2out ###
#set_false_path -from [get_ports "boot_addr_i*"]   -to [get_ports "instr_addr_o*"] 
#set_false_path -from [get_ports "data_rvalid_i"]  -to [get_ports "data_req_o"]
#set_false_path -from [get_ports "instr_rvalid_i"] -to [get_ports "instr_req_o"]
#set_multicycle_path 2 -setup -from [get_ports "data_rvalid_i"]  -to [get_ports "data_req_o"]
set_multicycle_path 3 -setup -from [get_ports "boot_addr_i*"]   -to [get_ports "instr_addr_o*"]
set_multicycle_path 3 -setup -from [get_ports "instr_rvalid_i"] -to [get_ports "instr_req_o"]

set_false_path -hold -from [get_ports "boot_addr_i*"]   -to [get_ports "instr_addr_o*"] 
set_false_path -hold -from [get_ports "data_rvalid_i"]  -to [get_ports "data_req_o"]
set_false_path -hold -from [get_ports "instr_rvalid_i"] -to [get_ports "instr_req_o"]



## Max transition and fanout
set_max_fanout  	128 	[current_design]
set_max_transition 	0.250 	[current_design]

