# Copyright 2024 Dolphin Design
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the "License");
# you may not use this file except in compliance with the License, or,
# at your option, the Apache License version 2.0.
# You may obtain a copy of the License at
#
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

##################################################################################
#                                                                                #
# Contributors: Yoann Pruvost, Dolphin Design <yoann.pruvost@dolphin.fr>         #
#                                                                                #
# Description:  Makefile for CV32E40P Formal code analysis                       #
#                                                                                #
##################################################################################

export DESIGN_RTL_DIR = ../../rtl

create_lib:
	rm -rf work
	vlib work

compile_design: create_lib
	vlog -sv -f ../../cv32e40p_fpu_manifest.flist
	vlog -sv -mfcu -cuname cv32e40p_bind -f cv32e40p_formal.flist

compile_design_pulp: create_lib
	vlog -sv +define+PULP -f ../../cv32e40p_fpu_manifest.flist
	vlog -sv +define+PULP -mfcu -cuname cv32e40p_bind -f cv32e40p_formal.flist

compile_design_pulp_f0: create_lib
	vlog -sv +define+PULP_F0 -f ../../cv32e40p_fpu_manifest.flist
	vlog -sv +define+PULP_F0 -mfcu -cuname cv32e40p_bind -f cv32e40p_formal.flist

run: compile_design
	qverify -c -do formal.do

run_pulp: compile_design_pulp
	qverify -c -do formal.do

run_pulp_F0: compile_design_pulp_f0
	qverify -c -do formal.do

clean:
	qverify_clean
	rm -rf work