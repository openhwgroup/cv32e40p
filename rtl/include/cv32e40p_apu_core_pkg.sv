// Copyright 2024 OpenHW Group and Dolphin Design
// Copyright 2018 ETH Zurich and University of Bologna.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License");
// you may not use this file except in compliance with the License, or,
// at your option, the Apache License version 2.0.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
// Description:    Core package for APU/CVFPU interface                       //
////////////////////////////////////////////////////////////////////////////////

package cv32e40p_apu_core_pkg;

  // APU interface
  parameter APU_NARGS_CPU = 3;
  parameter APU_WOP_CPU = 6;
  parameter APU_NDSFLAGS_CPU = 15;
  parameter APU_NUSFLAGS_CPU = 5;

endpackage  // cv32e40p_apu_core_pkg
