// Copyright 2024 Cirrus Logic
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

set DESIGN_RTL_DIR ../../rtl

analyze -sv -f ../../cv32e40p_fpu_manifest.flist
analyze -sva -f cv32e40p_formal.flist

elaborate -top cv32e40p_formal_top

#Set up clocks and reset
clock clk_i
reset ~rst_ni

# Get design information to check general complexity
get_design_info

#Prove properties
prove -all

#Report proof results
report

