set HOME "../"
set DIRECTORY "rtl"
set REPORT_DIR "syn/reports"

# Set search and library paths
set_app_var search_path ${HOME}/${DIRECTORY}

###rvt testing-linkpath
#set_app_var link_path /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_tt0p78v25c.db
set_app_var link_path /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_ss0p75v125c.db

###lvt testing-linkpath
#set_app_var link_path /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_lvt/db_ccs/saed32lvt_ss0p75v125c.db

###hvt testing-linkpath
#set_app_var link_path /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_hvt/db_ccs/saed32hvt_ss0p75v125c.db

#set_app_var link_path [list \
  /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_ss0p75v125c.db \
  /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_lvt/db_ccs/saed32lvt_ss0p75v125c.db \
  /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_hvt/db_ccs/saed32hvt_ss0p75v125c.db ]

#set_app_var target_library /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_tt0p78v25c.db
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
set DESIGN_NAME "cv32e40p_controller"

# Analyze the Verilog source file

analyze -format sverilog "../rtl/include/cv32e40p_pkg.sv ../rtl/cv32e40p_controller.sv"

# Elaborate the design
elaborate ${DESIGN_NAME} -architecture verilog -library DEFAULT

# Link the design to ensure all references are resolved
link

# Flatten the hierarchy to ensure all submodules are ungrouped
ungroup -all -flatten -simple_names

# Constraints - since there's no top level clock port, we skip timing constraints for now
create_clock -name "clk" -period 5 -waveform {0 1} [get_ports clk]

#set clk_uncertainty and input/output delays
set_propagated_clock [get_clocks clk]
set_dont_touch_network [get_clocks clk]

# Input delays for setup (you can add multiple as needed)
set_input_delay 0.1 -max -rise -clock clk [get_ports *]
set_input_delay 0.1 -max -fall -clock clk [get_ports *]

#Output delays
set_output_delay 0.1 -max -clock clk [get_ports *]
set_output_delay 0.1 -max -clock clk [get_ports *]

# Optional: Setup clock uncertainty
set_clock_uncertainty 0.2 -setup [get_clocks clk]
set_clock_uncertainty 0.2 -hold [get_clocks clk]


# General design constraints

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
