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

.. _performance-counters:

Performance Counters
====================

CV32E40P implements performance counters according to the RISC-V Privileged Specification, version 1.11 (see Hardware Performance Monitor, Section 3.1.11).
The performance counters are placed inside the Control and Status Registers (CSRs) and can be accessed with the ``CSRRW(I)`` and ``CSRRS/C(I)`` instructions.

CV32E40P implements the clock cycle counter ``mcycle(h)``, the retired instruction counter ``minstret(h)``, as well as the parameterizable number of event counters
``mhpmcounter3(h)`` - ``mhpmcounter31(h)`` and the corresponding event selector CSRs ``mhpmevent3`` - ``mhpmevent31``, and the ``mcountinhibit`` CSR to individually enable/disable the counters.
``mcycle(h)`` and ``minstret(h)`` are always available.

All counters are 64 bit wide.

The number of event counters is determined by the parameter ``NUM_MHPMCOUNTERS`` with a range from 0 to 29 (default value of 1).

Unimplemented counters always read 0.

.. note::

   All performance counters are using the gated version of ``clk_i``. The **wfi** instruction, the
   **cv.elw** instruction, and ``pulp_clock_en_i`` impact the gating of ``clk_i`` as explained
   in :ref:`sleep_unit` and can therefore affect the counters.

.. _event_selector:

Event Selector
--------------

The following events can be monitored using the performance counters of CV32E40P.

.. table:: Event Selector
  :name: Event Selector
  :widths: 10 20 65
  :class: no-scrollbar-table

  +-------------+-----------------+-------------------------------------------+
  | **Bit #**   | **Event Name**  | **Description**                           |
  +=============+=================+===========================================+
  | 0           | CYCLES          | Number of cycles                          |
  +-------------+-----------------+-------------------------------------------+
  | 1           | INSTR           | Number of instructions retired            |
  +-------------+-----------------+-------------------------------------------+
  | 2           | LD_STALL        | Number of load use hazards                |
  +-------------+-----------------+-------------------------------------------+
  | 3           | JMP_STALL       | Number of jump register hazards           |
  +-------------+-----------------+-------------------------------------------+
  | 4           | IMISS           | Cycles waiting for instruction fethces,   |
  |             |                 | excluding jumps and branches              |
  +-------------+-----------------+-------------------------------------------+
  | 5           | LD              | Number of load instructions               |
  +-------------+-----------------+-------------------------------------------+
  | 6           | ST              | Number of store instructions              |
  +-------------+-----------------+-------------------------------------------+
  | 7           | JUMP            | Number of jumps (unconditional)           |
  +-------------+-----------------+-------------------------------------------+
  | 8           | BRANCH          | Number of branches (conditional)          |
  +-------------+-----------------+-------------------------------------------+
  | 9           | BRANCH_TAKEN    | Number of branches taken (conditional)    |
  +-------------+-----------------+-------------------------------------------+
  | 10          | COMP_INSTR      | Number of compressed instructions retired |
  +-------------+-----------------+-------------------------------------------+
  | 11          | PIPE_STALL      | Cycles from stalled pipeline              |
  +-------------+-----------------+-------------------------------------------+
  | 12          | APU_TYPE        | Numbe of type conflicts on APU/FP         |
  +-------------+-----------------+-------------------------------------------+
  | 13          | APU_CONT        | Number of contentions on APU/FP           |
  +-------------+-----------------+-------------------------------------------+
  | 14          | APU_DEP         | Number of dependency stall on APU/FP      |
  +-------------+-----------------+-------------------------------------------+
  | 15          | APU_WB          | Number of write backs on APUB/FP          |
  +-------------+-----------------+-------------------------------------------+

The event selector CSRs ``mhpmevent3`` - ``mhpmevent31`` define which of these events are counted by the event counters ``mhpmcounter3(h)`` - ``mhpmcounter31(h)``.
If a specific bit in an event selector CSR is set to 1, this means that events with this ID are being counted by the counter associated with that selector CSR.
If an event selector CSR is 0, this means that the corresponding counter is not counting any event.

.. note::

   At most 1 bit should be set in an event selector. If multiple bits are set in an event selector, then the operation of the associated counter is undefined.


Controlling the counters from software
--------------------------------------

By default, all available counters are disabled after reset in order to provide the lowest power consumption.

They can be individually enabled/disabled by overwriting the corresponding bit in the ``mcountinhibit`` CSR at address ``0x320`` as described in the RISC-V Privileged Specification,
version 1.11 (see Machine Counter-Inhibit CSR, Section 3.1.13).
In particular, to enable/disable ``mcycle(h)``, bit 0 must be written. For ``minstret(h)``, it is bit 2. For event counter ``mhpmcounterX(h)``, it is bit X.

The lower 32 bits of all counters can be accessed through the base register, whereas the upper 32 bits are accessed through the ``h``-register.
Reads of all these registers are non-destructive.

Parametrization at synthesis time
---------------------------------

The ``mcycle(h)`` and ``minstret(h)`` counters are always available and 64 bit wide.

The number of available event counters ``mhpmcounterX(h)`` can be controlled via the ``NUM_MHPMCOUNTERS`` parameter.
By default ``NUM_MHPCOUNTERS`` set to 1.

An increment of 1 to the NUM_MHPCOUNTERS results in the addition of the following:

   - 64 flops for ``mhpmcounterX``
   - 15 flops for `mhpmeventX`
   -  1 flop  for `mcountinhibit[X]`
   - Adder and event enablement logic

Time Registers (``time(h)``)
----------------------------

The user mode ``time(h)`` registers are not implemented. Any access to these
registers will cause an illegal instruction trap. It is recommended that a software trap handler is
implemented to detect access of these CSRs and convert that into access of the
platform-defined ``mtime`` register (if implemented in the platform).
