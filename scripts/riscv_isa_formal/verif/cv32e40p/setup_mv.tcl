# Copyright 2024 Siemens
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

if {![info exists ::env(DESIGN_RTL_DIR)]} {
	set ::env(DESIGN_RTL_DIR) [pwd]/rtl
}
set_read_hdl_option -verilog_version sv2012 -pragma_ignore {translate_}
vlog -sv -f cv32e40p_fpu_manifest.flist
elaborate 
compile
set_mode mv
