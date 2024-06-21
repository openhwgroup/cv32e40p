#!/bin/bash
#
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

# This script is a template representing a customization to integrate OneSpin 360 with VCS simulator
#
# onespin calls the script as follows:
# template_vcs_flow.sh <args>
#
# In this script you need to set up the environment for the simulator,
#
ARG1=$1

vsim -64 -c -do "source ${ARG1}; quit -f"
