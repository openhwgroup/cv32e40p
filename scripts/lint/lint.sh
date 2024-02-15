#!/usr/bin/env bash

# Copyright 2023 OpenHW Group
# Copyright 2023 Dolphin Design
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Contributor: Pascal Gouedo <pascal.gouedo@dolphin.fr>

if [[ $# -eq 0 ]]; then 
  CONFIG=config_0p_0f_0z_0lat_0c
else
  CONFIG=config_$1
  if [[ ! -d $CONFIG ]]; then
    echo "Config $CONFIG does not exists."
    exit
  fi
fi
echo "Lint of $CONFIG"

if [[ -d questa_autocheck/$CONFIG ]]; then
  rm -rf questa_autocheck/$CONFIG
fi
mkdir -p questa_autocheck/$CONFIG

# Creating RTL file list
if [[ $CONFIG == *1f* ]]; then
  MANIFEST=cv32e40p_fpu_manifest
else
  MANIFEST=cv32e40p_manifest
fi

UPSTREAM_DIR=$(pwd)/../../rtl
echo "$upstream_dir" 
sed -n '/^+incdir+/s:${DESIGN_RTL_DIR}:'"$UPSTREAM_DIR"':p' ../../$MANIFEST.flist > questa_autocheck/$CONFIG/inc_design.f
sed -n '1,/cv32e40p_sim_clock_gate/{s:^${DESIGN_RTL_DIR}:'"$UPSTREAM_DIR"':p}' ../../$MANIFEST.flist > questa_autocheck/$CONFIG/src_design.f
echo "$(pwd)/$CONFIG/cv32e40p_config_pkg.sv" >> questa_autocheck/$CONFIG/src_design.f
echo "$(pwd)/cv32e40p_wrapper.sv" >> questa_autocheck/$CONFIG/src_design.f

cd questa_autocheck/$CONFIG

# Compiling Verilog / SystemVerilog RTL files
vlog -64 -nologo -source -timescale "1 ns / 1 ps" -sv -f inc_design.f -f src_design.f -assertdebug -work design_lib |& tee compile_design.log

# Launching formal lint analysis
qverify -licq -c -od formal_lint_out -do ../../qverify_analysis.do |& tee formal_lint.log 

# Launching formal lint AutoCheck Summary
qverify -licq -c -od formal_lint_out -do ../../qverify_autocheck.do

