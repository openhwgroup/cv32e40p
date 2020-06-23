# Copyright 2017 Embecosm Limited <www.embecosm.com>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Makefile for Verilator model of RI5CY
# Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>

# Tools

VERILATOR = verilator
VDIR = obj_dir
CPPFLAGS = -I$(VDIR) `pkg-config --cflags verilator`
CXXFLAGS = -Wall -Werror -std=c++11 -Wno-aligned-new
CXX = g++
LD = g++

# Testbench

SRC = testbench.cpp

OBJS = testbench.o

EXE = testbench

# top module name

TOP = top

# Verilator elements

VSRC = dp_ram.sv                                 \
       ram.sv                                    \
       top.sv                                    \
       ../../rtl/fpnew/src/fpnew_pkg.sv          \
       ../../rtl/include/cv32e40p_apu_core_package.sv     \
       ../../rtl/include/cv32e40p_defines.sv        \
       ../../rtl/include/cv32e40p_tracer_defines.sv \
       ../../rtl/cv32e40p_register_file_test_wrap.sv      \
       ../../rtl/cv32e40p_sim_clock_gate.sv      \
       ../../rtl/cv32e40p_alu.sv                    \
       ../../rtl/cv32e40p_alu_div.sv                \
       ../../rtl/cv32e40p_compressed_decoder.sv     \
       ../../rtl/cv32e40p_controller.sv             \
       ../../rtl/cv32e40p_cs_registers.sv           \
       ../../rtl/cv32e40p_decoder.sv                \
       ../../rtl/cv32e40p_int_controller.sv         \
       ../../rtl/cv32e40p_ex_stage.sv               \
       ../../rtl/cv32e40p_hwloop_controller.sv      \
       ../../rtl/cv32e40p_hwloop_regs.sv            \
       ../../rtl/cv32e40p_id_stage.sv               \
       ../../rtl/cv32e40p_if_stage.sv               \
       ../../rtl/cv32e40p_load_store_unit.sv        \
       ../../rtl/cv32e40p_mult.sv                   \
       ../../rtl/cv32e40p_prefetch_buffer.sv        \
       ../../rtl/cv32e40p_register_file_ff.sv       \
       ../../rtl/cv32e40p_core.sv                   \
       ../../rtl/cv32e40p_apu_disp.sv               \
       ../../rtl/cv32e40p_pmp.sv

VINC = ../../rtl/include

VOBJS = $(VDIR)/verilated.o       \
        $(VDIR)/verilated_vcd_c.o

VLIB = $(VDIR)/V$(TOP)__ALL.a

VSMK = V$(TOP).mk
VMK  = $(VDIR)/$(VSMK)

# Build the executable
all: $(EXE)

$(EXE): $(VLIB) $(VOBJS) $(OBJS)
	$(LD) -o $@ $(OBJS) $(VLIB) $(VOBJS)

$(VOBJS): $(VMK)
	for f in $@; \
	do \
		sf=$$(basename $$f); \
		$(MAKE) -C $(VDIR) -f $(VSMK) $$sf; \
	done

$(VLIB): $(VMK)
	make -C $(VDIR) -f V$(TOP).mk

$(VDIR)/$(TOP): $(VDIR) $(VMK)
	$(MAKE) -C $(VDIR) -f $(VSMK)

$(VDIR):
	mkdir -p $@

$(VMK): $(VSRC)
	verilator -O3 -CFLAGS "-O3 -g3 -std=gnu++11" \
                  -Wno-CASEINCOMPLETE -Wno-LITENDIAN -Wno-UNOPT \
	          -Wno-UNOPTFLAT -Wno-WIDTH -Wno-fatal -Wno-BLKANDNBLK \
		  --top-module top \
	          --Mdir $(VDIR) --trace -DPULP_FPGA_EMUL -cc \
	          +incdir+$(VINC) $(VSRC) $(SRC) --exe


.PHONY: clean
clean:
	$(RM) -r $(VDIR)
	$(RM) $(EXE) $(OBJS)
