# Copyright 2019 Clifford Wolf
# Copyright 2019 Robert Balas
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
# REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
# AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
# INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
# LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
# OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
# PERFORMANCE OF THIS SOFTWARE.

# Author: Robert Balas (balasr@iis.ee.ethz.ch)
#
# Description: Makefile for running the following examples:
#
#              - 'Hello World' (custom), command line 'make custom-vsim-run'
#              - 'Floating Point example' (custom_fp), command line 'make custom-fp-vsim-run'
#              - 'Interrupt example' (interrupt), command line 'make interrupt-vsim-run'

MAKE			= make

# vsim configuration
VVERSION                = "10.7b"

VLIB			= vlib-$(VVERSION)
VWORK			= work

VLOG			= vlog-$(VVERSION)
VLOG_FLAGS		= -pedanticerrors -suppress 2577 -suppress 2583 -define CV32E40P_TRACE_EXECUTION
VLOG_LOG                = vloggy

VOPT			= vopt-$(VVERSION)
VOPT_FLAGS		= -debugdb -fsmdebug -pedanticerrors +acc #=mnprft

VSIM			= vsim-$(VVERSION)
VSIM_HOME               = /usr/pack/modelsim-$(VVERSION)-kgf/questasim
VSIM_FLAGS              =  # user defined
ALL_VSIM_FLAGS		= $(VSIM_FLAGS)
VSIM_DEBUG_FLAGS	= -debugdb
VSIM_GUI_FLAGS          = -gui -debugdb
VSIM_SCRIPT             = vsim.tcl

# RTL source files
RTLSRC_HOME             := ../..
export DESIGN_RTL_DIR = $(RTLSRC_HOME)/rtl
CV_CORE_MANIFEST    := $(RTLSRC_HOME)/cv32e40p_manifest.flist
RTLSRC_TB_PKG		:= include/perturbation_pkg.sv
RTLSRC_TB_TOP		:= tb_top.sv
RTLSRC_TB		:= $(filter-out cv32e40p_fp_wrapper.sv,\
				$(wildcard *.sv))

RTLSRC_FPNEW_TB		:= $(wildcard *.sv)
RTLSRC_FPNEW_INCDIR	:= $(RTLSRC_HOME)/rtl/fpnew/src/common_cells/include
RTLSRC_FPNEW_PKG	:= $(RTLSRC_HOME)/rtl/fpnew/src/fpu_div_sqrt_mvp/hdl/defs_div_sqrt_mvp.sv $(RTLSRC_HOME)/rtl/fpnew/src/fpnew_pkg.sv $(RTLSRC_HOME)/rtl/fpnew/src/common_cells/src/cf_math_pkg.sv
RTLSRC_FPNEW		:= $(filter-out $(RTLSRC_HOME)/rtl/fpnew/src/fpnew_pkg.sv, $(wildcard $(RTLSRC_HOME)/rtl/fpnew/src/*.sv)) \
				$(filter-out $(RTLSRC_HOME)/rtl/fpnew/src/fpu_div_sqrt_mvp/hdl/defs_div_sqrt_mvp.sv, $(wildcard $(RTLSRC_HOME)/rtl/fpnew/src/fpu_div_sqrt_mvp/hdl/*.sv)) \
				 $(RTLSRC_HOME)/rtl/fpnew/src//common_cells/src/rr_arb_tree.sv  $(RTLSRC_HOME)/rtl/fpnew/src/common_cells/src/lzc.sv

RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(RTLSRC_TB_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

# riscv toolchain install path
RISCV                    ?= ~/.riscv
RISCV_EXE_PREFIX         = $(RISCV)/bin/riscv32-unknown-elf-

# assume vsim if no target chosen
.DEFAULT_GOAL := custom-vsim-run

# GCC configuration
CUSTOM_GCC_FLAGS           =

all: custom-vsim-run

# vsim testbench compilation and optimization
vlib: .lib-rtl

.lib-rtl:
	$(VLIB) $(VWORK)
	touch .lib-rtl

# rebuild if we change some sourcefile
.build-rtl: .lib-rtl $(CV_CORE_MANIFEST) $(RTLSRC_TB_PKG) $(RTLSRC_TB)
	$(VLOG) -work $(VWORK) $(VLOG_FLAGS) \
	-f $(CV_CORE_MANIFEST) $(RTLSRC_TB_PKG) $(RTLSRC_TB)
	touch .build-rtl

vsim-all: .opt-rtl

.opt-rtl: .build-rtl
	$(VOPT) -work $(VWORK) $(VOPT_FLAGS) $(RTLSRC_VLOG_TB_TOP) -o \
	$(RTLSRC_VOPT_TB_TOP)
	touch .opt-rtl

# fpnew dependencies
check_fpnew_deps:
	@if [ ! -d ../../rtl/fpnew ]; then echo Please run \'make fpnew_deps\' first to clone the required fpnew repos; exit 1; fi

fpnew_deps:
	if [ ! -d ../../rtl/fpnew ]; then git clone https://github.com/pulp-platform/fpnew ../../rtl/fpnew --recurse; fi

# rebuild if we change some sourcefile
.build-rtl-fp: .lib-rtl $(RTLSRC_FPNEW_PKG) $(RTLSRC_FPNEW) $(CV_CORE_MANIFEST) $(RTLSRC_TB_PKG) $(RTLSRC_FPNEW_TB)
	$(VLOG) -work $(VWORK) +incdir+$(RTLSRC_FPNEW_INCDIR) $(VLOG_FLAGS) \
	 $(RTLSRC_FPNEW_PKG) $(RTLSRC_FPNEW) -f $(CV_CORE_MANIFEST) $(RTLSRC_TB_PKG) $(RTLSRC_FPNEW_TB)
	touch .build-rtl-fp

vsim-all-fp: check_fpnew_deps .opt-rtl-fp

.opt-rtl-fp: .build-rtl-fp
	$(VOPT) -work $(VWORK) $(VOPT_FLAGS) -g FPU=1 $(RTLSRC_VLOG_TB_TOP) -o \
	$(RTLSRC_VOPT_TB_TOP)
	touch .opt-rtl-fp

vsim-all-pulp: .opt-rtl-pulp

.opt-rtl-pulp: .build-rtl
	$(VOPT) -work $(VWORK) $(VOPT_FLAGS) -g PULP_XPULP=1 $(RTLSRC_VLOG_TB_TOP) -o \
	$(RTLSRC_VOPT_TB_TOP)
	touch .opt-rtl-pulp


# run tb and exit
.PHONY: vsim-run
vsim-run: ALL_VSIM_FLAGS += -c
vsim-run: vsim-all
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do 'source $(VSIM_SCRIPT); exit -f'

# run tb and drop into interactive shell
.PHONY: vsim-run-sh
vsim-run-sh: ALL_VSIM_FLAGS += -c
vsim-run-sh: vsim-all
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT)

# run tb with simulator gui
.PHONY: vsim-run-gui
vsim-run-gui: ALL_VSIM_FLAGS += $(VSIM_GUI_FLAGS)
vsim-run-gui: vsim-all
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT)

.PHONY: tb-clean
tb-clean:
	if [ -d $(VWORK) ]; then rm -r $(VWORK); fi
	rm -f transcript vsim.wlf vsim.dbg trace_core*.log \
	.build-rtl .opt-rtl .lib-rtl *.vcd objdump

# run tb and exit
.PHONY: vsim-run-fp
vsim-run-fp: ALL_VSIM_FLAGS += -c
vsim-run-fp: vsim-all-fp
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) -GFPU=1 \
	$(RTLSRC_VOPT_TB_TOP) -do 'source $(VSIM_SCRIPT); exit -f'

# run tb and drop into interactive shell
.PHONY: vsim-run-sh-fp
vsim-run-sh-fp: ALL_VSIM_FLAGS += -c
vsim-run-sh-fp: vsim-all-fp
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT)

# run tb with simulator gui
.PHONY: vsim-run-gui-fp
vsim-run-gui-fp: ALL_VSIM_FLAGS += $(VSIM_GUI_FLAGS)
vsim-run-gui-fp: vsim-all-fp
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) -GFPU=1 \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT)

# run tb and exit
.PHONY: vsim-run-pulp
vsim-run-pulp: ALL_VSIM_FLAGS += -c
vsim-run-pulp: vsim-all-pulp
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) -GPULP_XPULP=1 \
	$(RTLSRC_VOPT_TB_TOP) -do 'source $(VSIM_SCRIPT); exit -f'


# run tb with simulator gui
.PHONY: vsim-run-gui-pulp
vsim-run-gui-pulp: ALL_VSIM_FLAGS += $(VSIM_GUI_FLAGS)
vsim-run-gui-pulp: vsim-all-pulp
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) -GPULP_XPULP=1 \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT)

.PHONY: tb-clean-fp
tb-clean-fp:
	if [ -d $(VWORK) ]; then rm -r $(VWORK); fi
	rm -rf transcript vsim.wlf vsim.dbg trace_core*.log \
	.build-rtl-fp .opt-rtl-fp .lib-rtl-fp *.vcd objdump

# rules to generate hex (loadable by simulators) from elf
%.hex: %.elf
	$(RISCV_EXE_PREFIX)objcopy -O verilog $< $@

%.dis: %.elf
	$(RISCV_EXE_PREFIX)objdump -S $^


# Running custom programs:
# This is an example for running a Hello World in the testbench
# We link with our custom crt0.s and syscalls.c against newlib so that we can
# use the c standard library
custom/hello_world.elf: custom/hello_world.c
	$(RISCV_EXE_PREFIX)gcc -march=rv32imc -o $@ -w -Os -g -nostdlib \
		$(CUSTOM_GCC_FLAGS) \
		-T custom/link.ld \
		-static \
		custom/crt0.S \
		$^ mem_stall/mem_stall.c custom/syscalls.c custom/vectors.S \
		-I $(RISCV)/riscv32-unknown-elf/include \
		-I mem_stall \
		-L $(RISCV)/riscv32-unknown-elf/lib \
		-lc -lm -lgcc
custom-clean:
	rm -rf custom/hello_world.elf custom/hello_world.hex

.PHONY: custom-vsim-run
custom-vsim-run: vsim-all custom/hello_world.hex
custom-vsim-run: ALL_VSIM_FLAGS += "+firmware=custom/hello_world.hex"
custom-vsim-run: vsim-run

.PHONY: custom-vsim-run-gui
custom-vsim-run-gui: vsim-all custom/hello_world.hex
custom-vsim-run-gui: ALL_VSIM_FLAGS += "+firmware=custom/hello_world.hex"
custom-vsim-run-gui: vsim-run-gui

# Running custom fp programs:
# This is an example for running a floating-point matrix multiplication in the testbench
# We link with our custom crt0.s and syscalls.c against newlib so that we can
# use the c standard library
custom_fp/main.elf: custom_fp/matmulNxN.c custom_fp/main.c
	$(RISCV_EXE_PREFIX)gcc -march=rv32imfc -mabi=ilp32f -o $@ -w -g -nostdlib \
		$(CUSTOM_GCC_FLAGS) \
		-T custom/link.ld  \
		-static \
		custom/crt0.S \
		$^ custom/syscalls.c custom/vectors.S \
		-I $(RISCV)/riscv32-unknown-elf/include \
		-L $(RISCV)/riscv32-unknown-elf/lib \
		-lc -lm -lgcc
custom-fp-clean:
	rm -rf custom_fp/main.elf custom_fp/main.hex

.PHONY: custom-fp-vsim-run
custom-fp-vsim-run: vsim-all-fp custom_fp/main.hex
custom-fp-vsim-run: ALL_VSIM_FLAGS += "+firmware=custom_fp/main.hex"
custom-fp-vsim-run: vsim-run-fp


.PHONY: custom-fp-vsim-run-gui
custom-fp-vsim-run-gui: vsim-all-fp custom_fp/main.hex
custom-fp-vsim-run-gui: ALL_VSIM_FLAGS += "+firmware=custom_fp/main.hex"
custom-fp-vsim-run-gui: vsim-run-gui-fp

# compile and run interrupt
interrupt/interrupt.elf: interrupt/interrupt.c
	$(RISCV_EXE_PREFIX)gcc -march=rv32imc -o $@ -w -Os -g -nostdlib \
		${CUSTOM_GCC_FLAGS} \
		-T custom/link.ld  \
		-static \
		custom/crt0.S \
		$^ mem_stall/mem_stall.c custom/syscalls.c interrupt/vectors.S \
		-I $(RISCV)/riscv32-unknown-elf/include \
		-I mem_stall/ \
		-L $(RISCV)/riscv32-unknown-elf/lib \
		-lc -lm -lgcc
interrupt-clean:
	rm -rf interrupt/interrupt.elf interrupt/interrupt.hex

.PHONY: interrupt-vsim-run
interrupt-vsim-run: vsim-all interrupt/interrupt.hex
interrupt-vsim-run: ALL_VSIM_FLAGS += "+firmware=interrupt/interrupt.hex"
interrupt-vsim-run: vsim-run

.PHONY: interrupt-vsim-run-gui

interrupt-vsim-run-gui: vsim-all interrupt/interrupt.hex
interrupt-vsim-run-gui: ALL_VSIM_FLAGS += "+firmware=interrupt/interrupt.hex"
interrupt-vsim-run-gui: vsim-run-gui

# Compile and run HW-loops test
# Until the compiler will correctly handle HW-loops, manually insert them (no jumps/branch in the body)
# Compile with "rv32imxpulpv2" with "-mnohwloop" or "-O0" to avoid the compiler inserting other hw-loops
# Do not use RVC, as the instructions should be aligned and not compressed
hwlp_test/hwlp_test.elf: hwlp_test/hwlp_test.c
	$(RISCV_EXE_PREFIX)gcc -march=rv32imxpulpv2 -mnohwloop -o $@ -w -O0 -g -nostdlib \
		$(CUSTOM_GCC_FLAGS) \
		-T custom/link.ld \
		-static \
		custom/crt0.S \
		$^ mem_stall/mem_stall.c custom/syscalls.c custom/vectors.S \
		-I $(RISCV)/riscv32-unknown-elf/include \
		-I mem_stall \
		-L $(RISCV)/riscv32-unknown-elf/lib \
		-lc -lm -lgcc
hwlp-clean:
	rm -rf hwlp_test/hwlp_test.elf hwlp_test/hwlp_test.hex

.PHONY: hwlp-vsim-run
hwlp-vsim-run: vsim-all-pulp hwlp_test/hwlp_test.hex
hwlp-vsim-run: ALL_VSIM_FLAGS += "+firmware=hwlp_test/hwlp_test.hex"
hwlp-vsim-run: vsim-run-pulp

.PHONY: hwlp-vsim-run-gui
hwlp-vsim-run-gui: vsim-all-pulp hwlp_test/hwlp_test.hex
hwlp-vsim-run-gui: ALL_VSIM_FLAGS += "+firmware=hwlp_test/hwlp_test.hex"
hwlp-vsim-run-gui: vsim-run-gui-pulp

# general targets
.PHONY: clean
clean: tb-clean tb-clean-fp custom-clean custom-fp-clean interrupt-clean hwlp-clean
