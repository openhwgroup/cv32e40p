##################################################################
##								##
##			BTA Design Services			##
##	Author	: 	Ludmila Rubin				##
##	Email	:	lrubin@btadesignservices.com		##
##      Date    :       Mar 19, 2020				##
##	Abstract: 	Genus synthesis settings		##
##			recommended for riscv_core		##
##								##
##################################################################


## Preset global variables and attributes
set_db / .source_verbose               	true
set_db / .source_verbose_info          	true
set_db / .information_level 		9

set_db / .timing_report_time_unit 	ns
set_db / .lp_power_unit 		uW


set_db / .hdl_track_filename_row_col            true   ;# Used for cross probing and datapath report. May be memory consuming


# Prevent auto ungrouping to make debugging easier. It is recommended to keep the default value for better optimization
#set_db / .auto_ungroup 			none

set_db / .tns_opto 				true 	;# Controls whether timing slack is optimized only on the most critical path or on other paths with negative slack

set_db / .optimize_constant_0_flops             true 	;# Allows constant 0 propogation through flip flops
set_db / .optimize_constant_1_flops             true 	;# Allows constant 1 propogation through flip flops
set_db / .delete_unloaded_seqs                  true 	;# Controls the deletion of unloaded sequential instances
set_db / .delete_unloaded_insts                 true
set_db / .optimize_merge_flops                  false
set_db / .optimize_constant_latches             true

set_db / .hdl_error_on_blackbox                 true
set_db / .remove_assigns                        true   	;# Allow incremental optimization when removing assign statements
set_db / .hdl_unconnected_value                 0
set_db / .hdl_max_loop_limit                    1800
set_db / .dp_analytical_opt                     standard ;# Effort level for global datapath optimization (off|standard|extreme)
## By default, Genus performs boundary optimization during synthesis for all modules in the design. The attribute is boundary_opto {true | false | strict_no}. Setting this attribute to false prevents ungrouping of the module.

## preserved nets involved in combinational loop(s)
set_db / .print_ports_nets_preserved_for_cb     true 	;# Print the list of preserved netlist point(s) involved in combinational loop(s)
set_db / .cb_preserve_ports_nets 		false  	;# Don't preserve netlist point(s) involved in combinational loop(s)


## Clock gating insertion
set_db / .lp_insert_clock_gating                true
set_db / .lp_clock_gating_prefix               	CLKG_


