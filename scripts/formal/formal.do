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

#//////////////////////////////////////////////////////////////////////////////////
#                                                                                //
# Contributors: Yoann Pruvost, Dolphin Design <yoann.pruvost@dolphin.fr>         //
#                                                                                //
# Description:  Formal script for CV32E40P                                       //
#                                                                                //
#//////////////////////////////////////////////////////////////////////////////////

set top cv32e40p_formal_top

#netlist clock clk_i -period 50

#netlist constraint rst_ni -value 1'b1 -after_init

#netlist port domain i_lint_grnt -clock i_clk

formal compile -d cv32e40p_formal_top -cuname cv32e40p_bind

formal verify -timeout 100m -jobs 4 -sanity_waveforms

#exit
