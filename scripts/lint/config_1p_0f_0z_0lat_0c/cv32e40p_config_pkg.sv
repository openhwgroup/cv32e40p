`ifndef CV32E40P_CONFIG_PKG
`define CV32E40P_CONFIG_PKG

package cv32e40p_config_pkg;

    parameter bit COREV_PULP           = 1;
    parameter bit COREV_CLUSTER        = 0;
    parameter bit FPU                  = 0;
    parameter int FPU_ADDMUL_LAT       = 0;
    parameter int FPU_OTHERS_LAT       = 0;
    parameter bit ZFINX                = 0;
    parameter int INSTR_ADDR_MEM_WIDTH = 13;
    parameter int DATA_ADDR_MEM_WIDTH  = 13;

endpackage

`endif


