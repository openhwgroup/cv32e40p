set HOME "cv32e40p"
set DIRECTORY "rtl"
set REPORT_DIR "syn/reports"

# Set search and library paths
set_app_var search_path ${HOME}/${DIRECTORY}
set_app_var link_path /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_lvt/db_ccs/saed32lvt_tt0p78v25c.db

#set_app_var link_path [list \ /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_ss0p75v125c.db \ /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_lvt/db_ccs/saed32lvt_ss0p75v125c.db \ /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_hvt/db_ccs/saed32hvt_ss0p75v125c.db ]

set_app_var target_library /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_lvt/db_ccs/saed32lvt_tt0p78v25c.db

#set_app_var target_library [list \ /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_rvt/db_ccs/saed32rvt_ss0p75v125c.db \ /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_lvt/db_ccs/saed32lvt_ss0p75v125c.db \ /usr/local/synopsys/pdk/SAED32_EDK/lib/stdcell_hvt/db_ccs/saed32hvt_ss0p75v125c.db ]



# Power grid settings
set dc_allow_rtl_pg       true
set mw_logic1_net "VDD"
set mw_logic0_net "VSS"

# Define the design name
set DESIGN_NAME     "cv32e40p_top"

# Analyze the Verilog source file
analyze -format sverilog "../rtl/include/cv32e40p_apu_core_pkg.sv ../rtl/cv32e40p_top.sv ../rtl/vendor/pulp_platform_common_cells/include/common_cells/registers.svh ../example_tb/core/amo_shim.sv  ../example_tb/core/include/perturbation_pkg.sv  ../rtl/include/cv32e40p_pkg.sv ../bhv/cv32e40p_sim_clock_gate.sv ../rtl/cv32e40p_sleep_unit.sv ../rtl/cv32e40p_prefetch_controller.sv ../rtl/cv32e40p_fifo.sv ../rtl/cv32e40p_obi_interface.sv ../rtl/cv32e40p_prefetch_buffer.sv ../rtl/cv32e40p_aligner.sv ../rtl/cv32e40p_compressed_decoder.sv ../rtl/cv32e40p_if_stage.sv ../rtl/include/cv32e40p_fpu_pkg.sv ../rtl/cv32e40p_register_file_ff.sv ../rtl/cv32e40p_decoder.sv ../rtl/cv32e40p_controller.sv ../rtl/cv32e40p_int_controller.sv ../rtl/cv32e40p_id_stage.sv ../rtl/cv32e40p_mult.sv ../rtl/cv32e40p_popcnt.sv ../rtl/cv32e40p_ff_one.sv ../rtl/cv32e40p_alu_div.sv ../rtl/cv32e40p_alu.sv ../rtl/cv32e40p_ex_stage.sv ../rtl/cv32e40p_load_store_unit.sv ../rtl/cv32e40p_cs_registers.sv ../rtl/cv32e40p_core.sv ../rtl/vendor/pulp_platform_fpnew/src/fpnew_pkg.sv ../rtl/vendor/pulp_platform_common_cells/src/cf_math_pkg.sv ../rtl/vendor/pulp_platform_fpnew/src/fpnew_noncomp.sv ../rtl/vendor/pulp_platform_common_cells/src/lzc.sv ../rtl/vendor/pulp_platform_common_cells/src/rr_arb_tree.sv ../rtl/vendor/pulp_platform_fpnew/src/fpnew_top.sv ../rtl/vendor/pulp_platform_fpnew/src/fpnew_opgroup_fmt_slice.sv ../rtl/vendor/pulp_platform_fpnew/src/fpnew_opgroup_block.sv"

# Elaborate the design
elaborate ${DESIGN_NAME} -architecture verilog -library DEFAULT

# Link the design to ensure all references are resolved
link

# Flatten the hierarchy to ensure all submodules are ungrouped
ungroup -all -flatten -simple_names

# Constraints
# Clock definition: 1000 ns period (1 MHz), 50% duty cycle
set clock_period 5.0

# Input delays for interrupts
set in_delay_irq          [expr $clock_period * 0.50] 
# Output delays for interrupt related signals
set out_delay_irq         [expr $clock_period * 0.25] 

# Input delays for early signals
set in_delay_early [expr $clock_period * 0.10] 

# OBI inputs delays
set in_delay_instr_gnt    [expr $clock_period * 0.80]
set in_delay_instr_rvalid [expr $clock_period * 0.80]
set in_delay_instr_rdata  [expr $clock_period * 0.80]

set in_delay_data_gnt     [expr $clock_period * 0.80]
set in_delay_data_rvalid  [expr $clock_period * 0.80]
set in_delay_data_rdata   [expr $clock_period * 0.80]

# OBI outputs delays
set out_delay_instr_req  [expr $clock_period * 0.60]
set out_delay_instr_addr [expr $clock_period * 0.60]

set out_delay_data_req   [expr $clock_period * 0.60]
set out_delay_data_we    [expr $clock_period * 0.60]
set out_delay_data_be    [expr $clock_period * 0.60]
set out_delay_data_addr  [expr $clock_period * 0.60]
set out_delay_data_wdata [expr $clock_period * 0.60]

# I/O delays for non RISC-V Bus Interface ports
set in_delay_other       [expr $clock_period * 0.10]
set out_delay_other      [expr $clock_period * 0.60]

# core_sleep_o output delay
set out_delay_core_sleep [expr $clock_period * 0.25]

# All clocks
set clock_ports [list \
    clk_i \
]

# IRQ Input ports
set irq_input_ports [remove_from_collection [get_ports irq_i*] [get_ports irq_id_o*]]

# IRQ Output ports
set irq_output_ports [list \
    irq_ack_o \
    irq_id_o* \
]

# Early Input ports (ideally from register)
set early_input_ports [list \
    debug_req_i \
    boot_addr_i* \
    mtvec_addr_i* \
    dm_halt_addr_i* \
    hart_id_i* \
    dm_exception_addr_i* \
]

# RISC-V OBI Input ports
set obi_input_ports [list \
    instr_gnt_i \
    instr_rvalid_i \
    instr_rdata_i* \
    data_gnt_i \
    data_rvalid_i \
    data_rdata_i* \
]

# RISC-V OBI Output ports
set obi_output_ports [list \
    instr_req_o \
    instr_addr_o* \
    data_req_o \
    data_we_o \
    data_be_o* \
    data_addr_o* \
    data_wdata_o* \
]

# RISC-V Sleep Output ports
set sleep_output_ports [list \
    core_sleep_o \
]

############## Defining default clock definitions ##############

create_clock \
      -name clk_i \
      -period $clock_period \
      [get_ports clk_i] 


########### Defining Default I/O constraints ###################

set all_clock_ports $clock_ports

set all_other_input_ports  [remove_from_collection [all_inputs]  [get_ports [list $all_clock_ports $obi_input_ports $irq_input_ports $early_input_ports]]]
set all_other_output_ports [remove_from_collection [all_outputs] [get_ports [list $all_clock_ports $obi_output_ports $sleep_output_ports $irq_output_ports]]]

# IRQs
set_input_delay  $in_delay_irq          [get_ports $irq_input_ports        ] -clock clk_i
set_output_delay $out_delay_irq         [get_ports $irq_output_ports       ] -clock clk_i

# OBI input/output delays
set_input_delay  $in_delay_instr_gnt    [ get_ports instr_gnt_i            ] -clock clk_i
set_input_delay  $in_delay_instr_rvalid [ get_ports instr_rvalid_i         ] -clock clk_i
set_input_delay  $in_delay_instr_rdata  [ get_ports instr_rdata_i*         ] -clock clk_i

set_input_delay  $in_delay_data_gnt     [ get_ports data_gnt_i             ] -clock clk_i
set_input_delay  $in_delay_data_rvalid  [ get_ports data_rvalid_i          ] -clock clk_i
set_input_delay  $in_delay_data_rdata   [ get_ports data_rdata_i*          ] -clock clk_i

set_output_delay $out_delay_instr_req   [ get_ports instr_req_o            ] -clock clk_i
set_output_delay $out_delay_instr_addr  [ get_ports instr_addr_o*          ] -clock clk_i

set_output_delay $out_delay_data_req    [ get_ports data_req_o             ] -clock clk_i
set_output_delay $out_delay_data_we     [ get_ports data_we_o              ] -clock clk_i
set_output_delay $out_delay_data_be     [ get_ports data_be_o*             ] -clock clk_i
set_output_delay $out_delay_data_addr   [ get_ports data_addr_o*           ] -clock clk_i
set_output_delay $out_delay_data_wdata  [ get_ports data_wdata_o*          ] -clock clk_i

# Misc
set_input_delay  $in_delay_early        [get_ports $early_input_ports      ] -clock clk_i
set_input_delay  $in_delay_other        [get_ports $all_other_input_ports  ] -clock clk_i

set_output_delay $out_delay_other       [get_ports $all_other_output_ports ] -clock clk_i
set_output_delay $out_delay_core_sleep  [ get_ports core_sleep_o           ] -clock clk_i


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