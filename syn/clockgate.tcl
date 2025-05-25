set HOME "../"
set DIRECTORY "rtl"
set REPORT_DIR "syn/reports"

# Set search and library paths
set_app_var search_path ${HOME}/${DIRECTORY}

###rvt testing-linkpath 
set_app_var link_path /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_ss0p75v125c.db

###lvt testing-linkpath
#set_app_var link_path /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_lvt/db_ccs/saed32lvt_ss0p75v125c.db

###hvt testing-linkpath
#set_app_var link_path /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_hvt/db_ccs/saed32hvt_ss0p75v125c.db




set_app_var target_library /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_ss0p75v125c.db


#set_app_var target_library /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_hvt/db_ccs/saed32hvt_ss0p75v125c.db
#set_app_var target_library [list \
  /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_ss0p75v125c.db \
  /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_lvt/db_ccs/saed32lvt_ss0p75v125c.db \
  /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_hvt/db_ccs/saed32hvt_ss0p75v125c.db ]



# Power grid settings
set dc_allow_rtl_pg       true
set mw_logic1_net "VDD"
set mw_logic0_net "VSS"

# Define the design name
set DESIGN_NAME     "cv32e40p_clock_gate"

# Analyze the Verilog source file
###analyze -format sverilog "../rtl/include/cv32e40p_apu_core_pkg.sv ../rtl/cv32e40p_top.sv ../rtl/vendor/pulp_platform_common_cells/include/common_cells/registers.svh ../example_tb/core/amo_shim.sv  ../example_tb/core/include/perturbation_pkg.sv  ../rtl/include/cv32e40p_pkg.sv ../bhv/cv32e40p_sim_clock_gate.sv ../rtl/cv32e40p_sleep_unit.sv ../rtl/cv32e40p_prefetch_controller.sv ../rtl/cv32e40p_fifo.sv ../rtl/cv32e40p_obi_interface.sv ../rtl/cv32e40p_prefetch_buffer.sv ../rtl/cv32e40p_aligner.sv ../rtl/cv32e40p_compressed_decoder.sv ../rtl/cv32e40p_if_stage.sv ../rtl/include/cv32e40p_fpu_pkg.sv ../rtl/cv32e40p_register_file_ff.sv ../rtl/cv32e40p_decoder.sv ../rtl/cv32e40p_controller.sv ../rtl/cv32e40p_int_controller.sv ../rtl/cv32e40p_id_stage.sv ../rtl/cv32e40p_mult.sv ../rtl/cv32e40p_popcnt.sv ../rtl/cv32e40p_ff_one.sv ../rtl/cv32e40p_alu_div.sv ../rtl/cv32e40p_alu.sv ../rtl/cv32e40p_ex_stage.sv ../rtl/cv32e40p_load_store_unit.sv ../rtl/cv32e40p_cs_registers.sv ../rtl/cv32e40p_core.sv ../rtl/vendor/pulp_platform_fpnew/src/fpnew_pkg.sv ../rtl/vendor/pulp_platform_common_cells/src/cf_math_pkg.sv ../rtl/vendor/pulp_platform_fpnew/src/fpnew_noncomp.sv ../rtl/vendor/pulp_platform_common_cells/src/lzc.sv ../rtl/vendor/pulp_platform_common_cells/src/rr_arb_tree.sv ../rtl/vendor/pulp_platform_fpnew/src/fpnew_top.sv ../rtl/vendor/pulp_platform_fpnew/src/fpnew_opgroup_fmt_slice.sv ../rtl/vendor/pulp_platform_fpnew/src/fpnew_opgroup_block.sv"


analyze -format sverilog "../bhv/cv32e40p_sim_clock_gate.sv"

# Elaborate the design
elaborate ${DESIGN_NAME} -architecture verilog -library DEFAULT

# Link the design to ensure all references are resolved
link

# Flatten the hierarchy to ensure all submodules are ungrouped
ungroup -all -flatten -simple_names

# Constraints
# Clock definition
create_clock -name "clk" -period 2 -waveform {0 1} [get_ports "clk_i"]
set_propagated_clock [get_clocks "clk"]
set_dont_touch_network [get_clocks "clk"]

# Input and output delays
set_input_delay 0.1 -max -rise -clock "clk" [get_ports "en_i"]
set_input_delay 0.1 -max -fall -clock "clk" [get_ports "scan_cg_en_i"]

set_output_delay 0.1 -max -clock "clk" [get_ports "clk_o"]

# Clock uncertainty for setup and hold times
set_clock_uncertainty 0.2 -setup [get_clocks "clk"]
set_clock_uncertainty 0.2 -hold [get_clocks "clk"]

# General design constraints
set_max_fanout 100 [get_designs "*"]
set_fix_multiple_port_nets -all -buffer_constants

# Check the design for issues
check_design

# Perform synthesis with optimization
compile_ultra -incremental

# Fix naming and hierarchy for output
change_names -rules verilog -hierarchy

# Write synthesized outputs
write -format ddc -output "${DESIGN_NAME}_synthesized.ddc"
write -format verilog -output "${DESIGN_NAME}_synthesized.v"
write_sdc -nosplit "${DESIGN_NAME}_const.sdc"
write_sdf "${DESIGN_NAME}_const.sdf"

# Generate reports
report_timing -transition_time -nets -attributes > ${HOME}/${REPORT_DIR}/${DESIGN_NAME}_timing_reports.log
report_qor > ${HOME}/${REPORT_DIR}/${DESIGN_NAME}_qor_reports.log
report_area -hierarchy > ${HOME}/${REPORT_DIR}/${DESIGN_NAME}_area_reports.log
report_power -hierarchy > ${HOME}/${REPORT_DIR}/${DESIGN_NAME}_power_reports.log
report_reference -hierarchy > ${HOME}/${REPORT_DIR}/${DESIGN_NAME}_reference_reports.log

# Exit the synthesis tool
exit