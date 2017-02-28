set IPS_PATH "../.."
set RTL_PATH "../../../rtl"
set IP      "riscv"
set IP_PATH "${IPS_PATH}/riscv"

set IP_LIST []
set IP_SEARCH_DIR []

lappend IP_SEARCH_DIR "$IP_PATH/include"
lappend IP_SEARCH_DIR "${RTL_PATH}/includes"

lappend IP_LIST "${IP_PATH}/include/riscv_defines.sv"
lappend IP_LIST "${IP_PATH}/include/apu_core_package.sv"
lappend IP_LIST "${IP_PATH}/apu_disp.sv"
lappend IP_LIST "${IP_PATH}/include/riscv_tracer_defines.sv"
lappend IP_LIST "${IP_PATH}/alu.sv"
lappend IP_LIST "${IP_PATH}/alu_basic.sv"
lappend IP_LIST "${IP_PATH}/alu_div.sv"
lappend IP_LIST "${IP_PATH}/compressed_decoder.sv"
lappend IP_LIST "${IP_PATH}/controller.sv"
lappend IP_LIST "${IP_PATH}/cs_registers.sv"
lappend IP_LIST "${IP_PATH}/debug_unit.sv"
lappend IP_LIST "${IP_PATH}/decoder.sv"
lappend IP_LIST "${IP_PATH}/exc_controller.sv"
lappend IP_LIST "${IP_PATH}/ex_stage.sv"
lappend IP_LIST "${IP_PATH}/hwloop_controller.sv"
lappend IP_LIST "${IP_PATH}/hwloop_regs.sv"
lappend IP_LIST "${IP_PATH}/id_stage.sv"
lappend IP_LIST "${IP_PATH}/if_stage.sv"
lappend IP_LIST "${IP_PATH}/load_store_unit.sv"
lappend IP_LIST "${IP_PATH}/mult.sv"
lappend IP_LIST "${IP_PATH}/prefetch_buffer.sv"
lappend IP_LIST "${IP_PATH}/prefetch_L0_buffer.sv"
lappend IP_LIST "${IP_PATH}/register_file.sv"
lappend IP_LIST "${IP_PATH}/riscv_core.sv"




vpx delete search path -all
vpx add search path -design $IP_SEARCH_DIR
vpx read design -enumconstraint -define SYNTHESIS  -golden -lastmod -noelab -systemverilog $IP_LIST


vpx elaborate design -golden -root riscv_core -rootonly