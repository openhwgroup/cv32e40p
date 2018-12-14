# Copyright 2018 Robert Balas
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.

# Author: Robert Balas (balasr@student.ethz.ch)
# Description: All in one. Uses parts of picorv32's makefile for handling the
# firmware

VERILATOR		= verilator

LINTER			= $(VERILATOR) --lint-only
MAKE			= make
CTAGS			= ctags

VVERSION                = "10.7b"

VLIB			= vlib-$(VVERSION)
VWORK			= work

VLOG			= vlog-$(VVERSION)
VLOG_FLAGS		= -pedanticerrors
VLOG_LOG                = vloggy

VOPT			= vopt-$(VVERSION)
VOPT_FLAGS		= -debugdb -fsmdebug -pedanticerrors +acc #=mnprft

VSIM			= vsim-$(VVERSION)
VSIM_FLAGS              =  # user defined
ALL_VSIM_FLAGS		= -c $(VSIM_FLAGS)
VSIM_DEBUG_FLAGS	= -debugdb
VSIM_GUI_FLAGS          = -gui -debugdb
VSIM_SCRIPT             = vsim.tcl

RTLSRC_HOME             := ../..
RTLSRC_TB_PKG		:=
RTLSRC_TB_TOP		:= $(wildcard tb_top.sv)
RTLSRC_TB		:= $(wildcard *.sv)
RTLSRC_INCDIR           := $(RTLSRC_HOME)/rtl/include/
RTLSRC_PKG		:= $(addprefix $(RTLSRC_HOME)/rtl/include/,\
				apu_core_package.sv riscv_defines.sv \
				riscv_tracer_defines.sv riscv_config.sv)
RTLSRC			:= $(wildcard $(RTLSRC_HOME)/rtl/*sv)
RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(RTLSRC_TB_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

# riscv toolchain install path
RISCV                    = ~/.local
RISCV_EXE_PREFIX         = $(RISCV)/bin/riscv32-unknown-elf-
FIRMWARE                 = picorv_firmware/
FIRMWARE_OBJS		 = $(addprefix picorv_firmware/, start.o irq.o \
				print.o sieve.o multest.o stats.o)
FIRMWARE_TEST_OBJS       = $(addsuffix .o, \
				$(basename $(wildcard picorv_tests/*.S)))

# # rtl related targets
# .PHONY: lint
# lint: $(RTLSRC_PKG) $(RTLSRC) $(RTLSRC_TB_PKG) $(RTLSRC_TB)
#	$(LINTER) -I. -Iinclude/ -Itb/ $(RTLSRC_PKG) $(RTLSRC) \
#		$(RTLSRC_TB_PKG) $(RTLSRC_TB)


# testbench compilation and optimization
vlib: .lib-rtl

.lib-rtl:
	$(VLIB) $(VWORK)
	touch .lib-rtl

# rebuild if we change some sourcefile
.build-rtl: .lib-rtl $(RTLSRC_PKG) $(RTLSRC) $(RTLSRC_TB_PKG) $(RTLSRC_TB)
	$(VLOG) -work $(VWORK) +incdir+$(RTLSRC_INCDIR) $(VLOG_FLAGS) \
	$(RTLSRC_PKG) $(RTLSRC) $(RTLSRC_TB_PKG) $(RTLSRC_TB)
	touch .build-rtl

tb-all: .opt-rtl

.opt-rtl: .build-rtl
	$(VOPT) -work $(VWORK) $(VOPT_FLAGS) $(RTLSRC_VLOG_TB_TOP) -o \
	$(RTLSRC_VOPT_TB_TOP)
	touch .opt-rtl

.PHONY: dpiheader
dpiheader: .build-tb
	$(VLOG) -work $(VWORK) -l $(VLOG_LOG) -dpiheader $(DPINAME) $(DPISRC)

# run tb and exit
.PHONY: tb-run
tb-run: tb-all
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do 'source $(VSIM_SCRIPT); exit -f'

# run tb and drop into interactive shell
.PHONY: tb-run-sh
tb-run-sh: tb-all
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT)

# run tb with simulator gui
.PHONY: tb-run-gui
tb-run-gui: ALL_VSIM_FLAGS += $(VSIM_GUI_FLAGS)
tb-run-gui: tb-run-sh

.PHONY: tb-clean
tb-clean:
	if [ -d $(VWORK) ]; then rm -r $(VWORK); fi
	rm -f transcript vsim.wlf vsim.dbg trace_core*.log .build-rtl .opt-rtl .lib-rtl

# compile and dump picorv firmware
picorv_firmware/firmware.hex: picorv_firmware/firmware.bin \
	picorv_firmware/makehex.py
	python3 picorv_firmware/makehex.py $< 16384 bin > $@

picorv_firmware/firmware.bin: picorv_firmware/firmware.elf
	$(RISCV_EXE_PREFIX)objcopy -O binary $< $@

picorv_firmware/firmware.elf: $(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) \
				picorv_firmware/sections.lds
	$(RISCV_EXE_PREFIX)gcc -Os -ffreestanding -nostdlib -o $@ \
		-Wl,-Bstatic,-T,picorv_firmware/sections.lds,-Map,picorv_firmware/firmware.map,--strip-debug \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) -lgcc

picorv_firmware/start.o: picorv_firmware/start.S
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32imc -o $@ $<

picorv_firmware/%.o: picorv_firmware/%.c
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32ic -Os --std=c99 -Wall \
		-ffreestanding -nostdlib -o $@ $<

picorv_tests/%.o: picorv_tests/%.S picorv_tests/riscv_test.h \
			picorv_tests/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32im -o $@ \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

# run picorv firmware
.PHONY: firmware-run
firmware-run: tb-all picorv_firmware/firmware.hex
firmware-run: ALL_VSIM_FLAGS += "+firmware=picorv_firmware/firmware.hex"
firmware-run: tb-run

.PHONY: firmware-run-gui
firmware-run-gui: tb-all picorv_firmware/firmware.hex
firmware-run-gui: ALL_VSIM_FLAGS = "+firmware=picorv_firmware/firmware.hex" \
				$(VSIM_GUI_FLAGS)
firmware-run-gui: tb-run-sh

.PHONY: firmware-clean
firmware-clean:
	rm -vrf $(addprefix picorv_firmware/firmware., elf bin hex map) \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS)

# general targets
.PHONY: clean
clean: tb-clean firmware-clean
