# Enable power analysis in PrimeTime
set power_enable_analysis TRUE

set target_library "/usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_tt0p78v25c.db"
set link_library [list {*} "/usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_tt0p78v25c.db"]

read_db $target_library

read_verilog "../syn/cv32e40p_mult_synthesized.v"

# Set top-level design
current_design cv32e40p_mult

# Create MHz clock
create_clock -period 35 -name clk [find port clk]

# Load VCD for switching activity
read_vcd -strip_path cv32e40p_mult_tb/u_cv32e40p_mult "../sim/cv32e40p_mult_tb.vcd"

# Save power reports
set DESIGN_NAME "cv32e40p_mult"
report_power -nosplit -verbose > ${DESIGN_NAME}_total_power.log
report_power -cell -verbose > ${DESIGN_NAME}_cell_power.log
report_switching_activity -list_not_annotated > ${DESIGN_NAME}_unannotated.log