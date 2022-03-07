#!/bin/bash

# Copyright 2021 OpenHW Group
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

if [ ! -d "./golden_reference_design" ]; then
  mkdir -p ./golden_reference_design
  cd ./golden_reference_design
  git clone git@github.com:openhwgroup/cv32e40p.git --branch cv32e40p_v1.0.0
  cd ../
fi
