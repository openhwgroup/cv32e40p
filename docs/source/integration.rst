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

.. _core-integration:

Core Integration
================

The main module is named ``cv32e40p_core`` and can be found in ``cv32e40p_core.sv``.
Below, the instantiation template is given and the parameters and interfaces are described.

Instantiation Template
----------------------

.. code-block:: verilog

  cv32e40p_core #(
      .FPU                      ( 0 ),
      .NUM_MHPMCOUNTERS         ( 1 ),
      .PULP_CLUSTER             ( 0 ),
      .PULP_XPULP               ( 0 ),
      .PULP_ZFINX               ( 0 )
  ) u_core (
      // Clock and reset
      .clk_i                    (),
      .rst_ni                   (),
      .scan_cg_en_i             (),

      // Configuration
      .boot_addr_i              (),
      .mtvec_addr_i             (),
      .dm_halt_addr_i           (),
      .dm_exception_addr_i      (),
      .hart_id_i                (),

      // Instruction memory interface
      .instr_req_o              (),
      .instr_gnt_i              (),
      .instr_rvalid_i           (),
      .instr_addr_o             (),
      .instr_rdata_i            (),

      // Data memory interface
      .data_req_o               (),
      .data_gnt_i               (),
      .data_rvalid_i            (),
      .data_addr_o              (),
      .data_be_o                (),
      .data_wdata_o             (),
      .data_we_o                (),
      .data_rdata_i             (),

      // Auxiliary Processing Unit (APU) interface
      .apu_req_o                (),
      .apu_gnt_i                (),
      .apu_operands_o           (),
      .apu_op_o                 (),
      .apu_flags_o              (),
      .apu_rvalid_i             (),
      .apu_result_i             (),
      .apu_flags_i              (),

       // Interrupt interface
      .irq_i                    (),
      .irq_ack_o                (),
      .irq_id_o                 (),

      // Debug interface
      .debug_req_i              (),
      .debug_havereset_o        (),
      .debug_running_o          (),
      .debug_halted_o           (),

      // Special control signals
      .fetch_enable_i           (),
      .core_sleep_o             (),
      .pulp_clock_en_i          ()
  );

Parameters
----------

.. note::
   The non-default (i.e. non-zero) settings of ``FPU``, ``PULP_CLUSTER``, ``PULP_XPULP`` and ``PULP_ZFINX`` have not
   been verified yet. The default parameter value for ``PULP_XPULP`` will be changed to 1 once it has been verified.
   The default configuration reflected below is currently under verification and this verification effort will be
   completed first.

.. note::
   The instruction encodings for the PULP instructions is expected to change in a non-backward-compatible manner, 
   see https://github.com/openhwgroup/cv32e40p/issues/452.

+------------------------------+-------------+------------+------------------------------------------------------------------+
| Name                         | Type/Range  | Default    | Description                                                      |
+==============================+=============+============+==================================================================+
| ``FPU``                      | bit         | 0          | Enable Floating Point Unit (FPU) support, see :ref:`fpu`         |
+------------------------------+-------------+------------+------------------------------------------------------------------+
| ``NUM_MHPMCOUNTERS``         | int (0..29) | 1          | Number of MHPMCOUNTER performance counters, see                  |
|                              |             |            | :ref:`performance-counters`                                      |
+------------------------------+-------------+------------+------------------------------------------------------------------+
| ``PULP_CLUSTER``             | bit         | 0          | Enable PULP Cluster support, see :ref:`pulp_cluster`             |
+------------------------------+-------------+------------+------------------------------------------------------------------+
| ``PULP_XPULP``               | bit         | 0          | Enable all of the custom PULP ISA extensions (except **cv.elw**) |
|                              |             |            | (see :ref:`custom-isa-extensions`) and all custom CSRs           |
|                              |             |            | (see :ref:`cs-registers`).                                       |
|                              |             |            |                                                                  |
|                              |             |            | Examples of PULP ISA                                             |
|                              |             |            | extensions are post-incrementing load and stores                 |
|                              |             |            | (see :ref:`corev_load_store`) and hardware loops                 |
|                              |             |            | (see :ref:`corev_hardware_loop`).                                |
|                              |             |            |                                                                  |
+------------------------------+-------------+------------+------------------------------------------------------------------+
| ``PULP_ZFINX``               | bit         | 0          | Enable Floating Point instructions to use the General Purpose    |
|                              |             |            | register file instead of requiring a dedicated Floating Point    |
|                              |             |            | register file, see :ref:`fpu`. Only allowed to be set to 1       |
|                              |             |            | if ``FPU`` = 1                                                   |
+------------------------------+-------------+------------+------------------------------------------------------------------+

Interfaces
----------

+-------------------------+-------------------------+-----+--------------------------------------------+
| Signal(s)               | Width                   | Dir | Description                                |
+=========================+=========================+=====+============================================+
| ``clk_i``               | 1                       | in  | Clock signal                               |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``rst_ni``              | 1                       | in  | Active-low asynchronous reset              |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``scan_cg_en_i``        | 1                       | in  | Scan clock gate enable. Design for test    |
|                         |                         |     | (DfT) related signal. Can be used during   |
|                         |                         |     | scan testing operation to force            |
|                         |                         |     | instantiated clock gate(s) to be enabled.  |
|                         |                         |     | This signal should be 0 during normal /    |
|                         |                         |     | functional operation.                      |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``boot_addr_i``         | 32                      | in  | Boot address. First program counter after  |
|                         |                         |     | reset = ``boot_addr_i``. Must be half-word |
|                         |                         |     | aligned. Do not change after enabling core |
|                         |                         |     | via ``fetch_enable_i``                     |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``mtvec_addr_i``        | 32                      | in  | ``mtvec`` address. Initial value for the   |
|                         |                         |     | address part of :ref:`csr-mtvec`.          |
|                         |                         |     | Do not change after enabling core          |
|                         |                         |     | via ``fetch_enable_i``                     |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``dm_halt_addr_i``      | 32                      | in  | Address to jump to when entering Debug     |
|                         |                         |     | Mode, see :ref:`debug-support`. Must be    |
|                         |                         |     | word-aligned. Do not change after enabling |
|                         |                         |     | core via ``fetch_enable_i``                |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``dm_exception_addr_i`` | 32                      | in  | Address to jump to when an exception       |
|                         |                         |     | occurs when executing code during Debug    |
|                         |                         |     | Mode, see :ref:`debug-support`. Must be    |
|                         |                         |     | word-aligned. Do not change after enabling |
|                         |                         |     | core via ``fetch_enable_i``                |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``hart_id_i``           | 32                      | in  | Hart ID, usually static, can be read from  |
|                         |                         |     | :ref:`csr-mhartid` and :ref:`csr-uhartid`  |
|                         |                         |     | CSRs                                       |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``instr_*``             | Instruction fetch interface, see :ref:`instruction-fetch`                  |
+-------------------------+----------------------------------------------------------------------------+
| ``data_*``              | Load-store unit interface, see :ref:`load-store-unit`                      |
+-------------------------+----------------------------------------------------------------------------+
| ``apu_*``               | Auxiliary Processing Unit (APU) interface, see :ref:`apu`                  |
+-------------------------+----------------------------------------------------------------------------+
| ``irq_*``               | Interrupt inputs, see :ref:`exceptions-interrupts`                         |
+-------------------------+----------------------------------------------------------------------------+
| ``debug_*``             | Debug interface, see :ref:`debug-support`                                  |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``fetch_enable_i``      | 1                       | in  | Enable the instruction fetch of CV32E40P.  |
|                         |                         |     | The first instruction fetch after reset    |
|                         |                         |     | de-assertion will not happen as long as    |
|                         |                         |     | this signal is 0. ``fetch_enable_i`` needs |
|                         |                         |     | to be set to 1 for at least one cycle      |
|                         |                         |     | while not in reset to enable fetching.     |
|                         |                         |     | Once fetching has been enabled the value   |
|                         |                         |     | ``fetch_enable_i`` is ignored.             |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``core_sleep_o``        | 1                       | out | Core is sleeping, see :ref:`sleep_unit`.   |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``pulp_clock_en_i``     | 1                       | in  | PULP clock enable (only used when          |
|                         |                         |     | ``PULP_CLUSTER`` = 1, tie to 0 otherwise), |
|                         |                         |     | see :ref:`sleep_unit`                      |
+-------------------------+-------------------------+-----+--------------------------------------------+
