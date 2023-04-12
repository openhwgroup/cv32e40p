..
   Copyright (c) 2023 OpenHW Group
   
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

.. _sleep_unit:

Sleep Unit
==========

Source File: :file:`rtl/cv32e40p_sleep_unit.sv`

The Sleep Unit contains and controls the instantiated clock gate (see :ref:`clock-gating-cell`) that gates ``clk_i`` and produces a gated clock
for use by the other modules inside CV32E40P. The Sleep Unit is the only place in which ``clk_i`` itself is used; all other modules use the gated version of ``clk_i``.

The clock gating in the Sleep Unit is impacted by the following:

 * ``rst_ni``
 * ``fetch_enable_i``
 * **wfi** instruction (only when ``COREV_CLUSTER`` = 0)
 * **cv.elw** instruction (only when ``COREV_CLUSTER`` = 1)
 * ``pulp_clock_en_i`` (only when ``COREV_CLUSTER`` = 1)

:numref:`Sleep Unit interface signals` describes the Sleep Unit interface.

.. table:: Sleep Unit interface signals
  :name: Sleep Unit interface signals
  :widths: 20 15 65
  :class: no-scrollbar-table

  +--------------------------------------+---------------+----------------------------------------------------+
  | **Signal**                           | **Direction** | **Description**                                    |
  +======================================+===============+====================================================+
  | ``pulp_clock_en_i``                  | input         | ``COREV_CLUSTER`` = 0:                             |
  |                                      |               |                                                    |
  |                                      |               | ``pulp_clock_en_i`` is not used. Tie to 0.         |
  |                                      |               +----------------------------------------------------+
  |                                      |               | ``COREV_CLUSTER`` = 1:                             |
  |                                      |               |                                                    |
  |                                      |               | ``pulp_clock_en_i`` can be used to gate ``clk_i``  |
  |                                      |               | internal to the core when ``core_sleep_o`` = 1.    |
  |                                      |               |                                                    |
  |                                      |               | See :ref:`pulp_cluster` for details.               |
  +--------------------------------------+---------------+----------------------------------------------------+
  | ``core_sleep_o``                     | output        | ``COREV_CLUSTER`` = 0:                             |
  |                                      |               |                                                    |
  |                                      |               | Core is sleeping because of a **wfi** instruction. |
  |                                      |               | If ``core_sleep_o`` = 1 then ``clk_i`` is gated    |
  |                                      |               | off internally and it is allowing to gate off      |
  |                                      |               | ``clk_i`` externally as well (e.g. FPU).           |
  |                                      |               |                                                    |
  |                                      |               | See :ref:`wfi` for details.                        |
  |                                      |               +----------------------------------------------------+
  |                                      |               | ``COREV_CLUSTER`` = 1:                             |
  |                                      |               |                                                    |
  |                                      |               | Core is sleeping because                           |
  |                                      |               | of a **cv.elw** instruction.                       |
  |                                      |               | If ``core_sleep_o`` = 1,                           |
  |                                      |               | then the ``pulp_clock_en_i`` directly              |
  |                                      |               | controls the internally instantiated clock gate    |
  |                                      |               | and therefore ``pulp_clock_en_i`` can be set       |
  |                                      |               | to 0 to internally gate off ``clk_i``. If          |
  |                                      |               | ``core_sleep_o`` = 0, then it is not allowed       |
  |                                      |               | to set ``pulp_clock_en_i`` to 0.                   |
  |                                      |               |                                                    |
  |                                      |               | See :ref:`pulp_cluster` for details.               |
  +--------------------------------------+---------------+----------------------------------------------------+

.. note::

   The semantics of ``pulp_clock_en_i`` and ``core_sleep_o`` depend on the ``COREV_CLUSTER`` parameter.

Startup behavior
----------------

``clk_i`` is internally gated off (while signaling ``core_sleep_o`` = 0) during CV32E40P startup:

 * ``clk_i`` is internally gated off during ``rst_ni`` assertion
 * ``clk_i`` is internally gated off from ``rst_ni`` deassertion until ``fetch_enable_i`` = 1

After initial assertion of ``fetch_enable_i``, the ``fetch_enable_i`` signal is ignored until after a next reset assertion.

.. _wfi:

WFI
---

The **wfi** instruction can under certain conditions be used to enter sleep mode awaiting a locally enabled
interrupt to become pending. The operation of **wfi** is unaffected by the global interrupt bits in **mstatus**.

A **wfi** will not enter sleep mode but will be executed as a regular **nop**, if any of the following conditions apply:

 * ``debug_req_i`` = 1 or a debug request is pending
 * The core is in debug mode
 * The core is performing single stepping (debug)
 * The core has a trigger match (debug)
 * ``COREV_CLUSTER`` = 1

If a **wfi** causes sleep mode entry, then ``core_sleep_o`` is set to 1 and ``clk_i`` is gated off internally.
``clk_i`` is allowed to be gated off externally as well in this scenario. A wake-up can be triggered by any of the following:

 * A locally enabled interrupt is pending
 * A debug request is pending
 * Core is in debug mode

Upon wake-up ``core_sleep_o`` is set to 0, ``clk_i`` will no longer be gated internally, must not be gated off externally, and
instruction execution resumes.

If one of the above wake-up conditions coincides with the **wfi** instruction, then sleep mode is not entered and ``core_sleep_o``
will not become 1.

:numref:`wfi-example` shows an example waveform for sleep mode entry because of a **wfi** instruction.

.. figure:: ../images/wfi.svg
   :name: wfi-example
   :align: center

   **wfi** example

.. _pulp_cluster:

PULP Cluster Extension
----------------------

CV32E40P has an optional extension to enable its usage in a PULP Cluster in the PULP (Parallel Ultra Low Power) platform.
This extension is enabled by setting the ``COREV_CLUSTER`` parameter to 1. The PULP platform is organized as clusters of
multiple (typically 4 or 8) CV32E40P cores that share a tightly-coupled data memory, aimed at running digital signal processing
applications efficiently.

The mechanism via which CV32E40P cores in a PULP Cluster synchronize with each other is implemented via the custom **cv.elw** instruction
that performs a read transaction on an external Event Unit (which for example implements barriers and semaphores). This
read transaction to the Event Unit together with the ``core_sleep_o`` signal inform the Event Unit that the CV32E40P is not busy and 
ready to go to sleep. Only in that case the Event Unit is allowed to set ``pulp_clock_en_i`` to 0, thereby gating off ``clk_i``
internal to the core. Once the CV32E40P core is ready to start again (e.g. when the last core meets the barrier), ``pulp_clock_en_i`` is
set to 1 thereby enabling the CV32E40P to run again.

If the PULP Cluster extension is not used (``COREV_CLUSTER`` = 0), the ``pulp_clock_en_i`` signal is not used and should be tied to 0.

Execution of a **cv.elw** instructions causes ``core_sleep_o`` = 1 only if all of the following conditions are met:
 
 * The **cv.elw** did not yet complete (which can be achieved by witholding ``data_gnt_i`` and/or ``data_rvalid_i``)
 * No debug request is pending
 * The core is not in debug mode
 * The core is not single stepping (debug)
 * The core does not have a trigger match (debug)

As ``pulp_clock_en_i`` can directly impact the internal clock gate, certain requirements are imposed on the environment of CV32E40P
in case ``COREV_CLUSTER`` = 1:

 * If ``core_sleep_o`` = 0, then ``pulp_clock_en_i`` must be 1
 * If ``pulp_clock_en_i`` = 0, then ``irq_i[*]`` must be 0           
 * If ``pulp_clock_en_i`` = 0, then ``debug_req_i`` must be 0    
 * If ``pulp_clock_en_i`` = 0, then ``instr_rvalid_i`` must be 0 
 * If ``pulp_clock_en_i`` = 0, then ``instr_gnt_i`` must be 0    
 * If ``pulp_clock_en_i`` = 0, then ``data_rvalid_i`` must be 0  
 * If ``pulp_clock_en_i`` = 0, then ``data_gnt_i`` must be 0

:numref:`load_event-example` shows an example waveform for sleep mode entry because of a **cv.elw** instruction.

.. figure:: ../images/load_event.svg
   :name: load_event-example
   :align: center

   **cv.elw** example
