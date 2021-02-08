..
   Copyright (c) 2020 OpenHW Group
   
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
  
   https://solderpad.org/licenses/
  
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
  
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

.. _getting-started:

Getting Started with CV32E40P
=============================

This page discusses initial steps and requirements to start using CV32E40P in your design.

Register File
-------------

CV32E40P comes with two different register file implementations.
Depending on the target technology, either the implementation in ``cv32e40p_register_file_ff.sv`` or the one in ``cv32e40p_register_file_latch.sv`` should be selected in the manifest file.
For more information about the two register file implementations and their trade-offs, check out :ref:`register-file`.

.. _clock-gating-cell:

Clock Gating Cell
-----------------

CV32E40P requires clock gating cells.
These cells are usually specific to the selected target technology and thus not provided as part of the RTL design.
A simulation-only version of the clock gating cell is provided in ``cv32e40p_sim_clock_gate.sv``. This file contains
a module called ``cv32e40p_clock_gate`` that has the following ports:

* ``clk_i``: Clock Input
* ``en_i``: Clock Enable Input
* ``scan_cg_en_i``: Scan Clock Gate Enable Input (activates the clock even though ``en_i`` is not set)
* ``clk_o``: Gated Clock Output

Inside CV32E40P, clock gating cells are used both in ``cv32e40p_sleep_unit.sv`` and ``cv32e40p_register_file_latch.sv``.
For more information on the expected behavior of the clock gating cell when using the latch-based register file check out :ref:`register-file`.

The ``cv32e40p_sim_clock_gate.sv`` file is not intended for synthesis. For ASIC synthesis and FPGA synthesis the manifest
should be adapted to use a customer specific file that implements the ``cv32e40p_clock_gate`` module using design primitives
that are appropriate for the intended synthesis target technology.

