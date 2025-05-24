# Midterm Readme

This document will tell you how to compile both the entire core on its own, as well as the submodules present in the report.

First, unzip the folder.

## Compiling the Core and Synthesizing it

Due to the extreme size of the core and the sheer number of files necessary, we left some of the folders unincorporated into sim, rtl, etc.

1. Navigate to `example_tb/core`
2. Run the following command.

```
vcs -sverilog tb_top.sv ../../rtl/vendor/pulp_platform_common_cells/include/common_cells/registers.svh amo_shim.sv ./include/perturbation_pkg.sv ../../rtl/include/cv32e40p_apu_core_pkg.sv ../../rtl/include/cv32e40p_pkg.sv ../../bhv/cv32e40p_sim_clock_gate.sv ../../rtl/cv32e40p_sleep_unit.sv ../../rtl/cv32e40p_prefetch_controller.sv ../../rtl/cv32e40p_fifo.sv ../../rtl/cv32e40p_obi_interface.sv ../../rtl/cv32e40p_prefetch_buffer.sv ../../rtl/cv32e40p_aligner.sv ../../rtl/cv32e40p_compressed_decoder.sv ../../rtl/cv32e40p_if_stage.sv ../../rtl/include/cv32e40p_fpu_pkg.sv ../../rtl/cv32e40p_register_file_ff.sv ../../rtl/cv32e40p_decoder.sv ../../rtl/cv32e40p_controller.sv ../../rtl/cv32e40p_int_controller.sv ../../rtl/cv32e40p_id_stage.sv ../../rtl/cv32e40p_mult.sv ../../rtl/cv32e40p_popcnt.sv ../../rtl/cv32e40p_ff_one.sv ../../rtl/cv32e40p_alu_div.sv ../../rtl/cv32e40p_alu.sv ../../rtl/cv32e40p_ex_stage.sv ../../rtl/cv32e40p_load_store_unit.sv ../../rtl/cv32e40p_cs_registers.sv ../../rtl/cv32e40p_core.sv ../../rtl/vendor/pulp_platform_fpnew/src/fpnew_pkg.sv ../../rtl/vendor/pulp_platform_common_cells/src/cf_math_pkg.sv ../../rtl/vendor/pulp_platform_fpnew/src/fpnew_noncomp.sv  ../../rtl/cv32e40p_top.sv ../../rtl/vendor/pulp_platform_common_cells/src/lzc.sv ../../rtl/vendor/pulp_platform_common_cells/src/rr_arb_tree.sv ../../rtl/vendor/pulp_platform_fpnew/src/fpnew_top.sv ../../rtl/vendor/pulp_platform_fpnew/src/fpnew_opgroup_fmt_slice.sv ../../rtl/vendor/pulp_platform_fpnew/src/fpnew_opgroup_block.sv cv32e40p_fp_wrapper.sv cv32e40p_random_interrupt_generator.sv cv32e40p_tb_subsystem.sv dp_ram.sv mm_ram.sv riscv_gnt_stall.sv riscv_rvalid_stall.sv -full64 -P /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/novas.tab /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/pli.a
```
3. For synthesis, navigate to `syn`, run Design Compiler and run the following:
```
source compile.tcl
```

4. Power Analysis is not possible given that the core testbench has yet to be revised to properly simulate things.



## Compiling the Chosen Submodules

### Simultation
Navigate to the `sim` folder.

For `cv32e40p_clock_gate`
```
cd ../sim
vcs -sverilog ../rtl/cv32e40p_sim_clock_gate.sv clock_gate_tb.sv -full64 -P /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/novas.tab /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/pli.a          
```

For `cv32e40p_mult`

```
vcs -sverilog ../rtl/include/cv32e40p_pkg.sv  ../rtl/cv32e40p_mult.sv mult_tb.sv -full64 -P /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/novas.tab /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/pli.a
```

For `cv32e40p_controller`

```
vcs -sverilog ../rtl/include/cv32e40p_pkg.sv ../rtl/cv32e40p_controller.sv controller_tb.sv -full64 -P /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/novas.tab /usr/local/synopsys/verdi/V-2023.12-SP2-5/share/PLI/VCS/LINUX64/pli.a
```

### Synthesis

Navigate to `syn/` and run Design Compiler.

1. To synthesize the clock gate, run `source clockgate.tcl`
2. To synthesize the multiplier, run `source mult.tcl`
3. To synthesize the controller, run `source controller.tcl`

### PrimeTime

Navigate to `ptpx/` and run PrimeTime

1. To analyze the clock gate, run `source clockgate.tcl`
2. To analyze the multiplier, run `source mult.tcl`
3. To analyze the controller, run `source controller.tcl`

