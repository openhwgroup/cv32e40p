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

Introduction
=============

CV32E40P is a 4-stage in-order 32-bit RISC-V
processor core. The ISA of CV32E40P
has been extended to support multiple additional instructions including
hardware loops, post-increment load and store instructions and
additional ALU instructions that are not part of the standard RISC-V
ISA. :numref:`blockdiagram` shows a block diagram of the core.

.. figure:: ../images/CV32E40P_Block_Diagram.png
   :name: blockdiagram
   :align: center
   :alt:

   Block Diagram of CV32E40P RISC-V Core

License
-------
Copyright 2020 OpenHW Group.

Copyright 2018 ETH Zurich and University of Bologna.

Copyright and related rights are licensed under the Solderpad Hardware
License, Version 0.51 (the “License”); you may not use this file except
in compliance with the License. You may obtain a copy of the License at
http://solderpad.org/licenses/SHL-0.51. Unless required by applicable
law or agreed to in writing, software, hardware and materials
distributed under this License is distributed on an “AS IS” BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Standards Compliance
--------------------

CV32E40P is a standards-compliant 32-bit RISC-V processor.
It follows these specifications:

* `RISC-V Instruction Set Manual, Volume I: User-Level ISA, Document Version 20191213 (December 13, 2019) <https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMAFDQC/riscv-spec-20191213.pdf>`_
* `RISC-V Instruction Set Manual, Volume II: Privileged Architecture, document version 20190608-Base-Ratified (June 8, 2019) <https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMFDQC-and-Priv-v1.11/riscv-privileged-20190608.pdf>`_.
  CV32E40P implements the Machine ISA version 1.11.
* `RISC-V External Debug Support, version 0.13.2 <https://content.riscv.org/wp-content/uploads/2019/03/riscv-debug-release.pdf>`_

Many features in the RISC-V specification are optional, and CV32E40P can be parametrized to enable or disable some of them.

CV32E40P supports the following base instruction set.

* The RV32I Base Integer Instruction Set, version 2.1

In addition, the following standard instruction set extensions are available.

.. list-table:: CV32E40P Standard Instruction Set Extensions
   :header-rows: 1

   * - Standard Extension
     - Version
     - Configurability

   * - **C**: Standard Extension for Compressed Instructions
     - 2.0
     - always enabled

   * - **M**: Standard Extension for Integer Multiplication and Division
     - 2.0
     - always enabled

   * - **Zicount**: Performance Counters
     - 2.0
     - always enabled

   * - **Zicsr**: Control and Status Register Instructions
     - 2.0
     - always enabled

   * - **Zifencei**: Instruction-Fetch Fence
     - 2.0
     - always enabled

   * - **F**: Single-Precision Floating-Point
     - 2.2
     - optionally enabled based on ``FPU`` parameter

The following custom instruction set extensions are available.

.. list-table:: CV32E40P Custom Instruction Set Extensions
   :header-rows: 1

   * - Custom Extension
     - Version
     - Configurability

   * - **Xcorev**: CORE-V ISA Extensions (excluding **cv.elw**)
     - 1.0
     - optionally enabled based on ``PULP_XPULP`` parameter

   * - **Xpulpcluster**: PULP Cluster Extension
     - 1.0
     - optionally enabled based on ``PULP_CLUSTER`` parameter

   * - **Xpulpzfinx**: PULP Share Integer (X) Registers with Floating Point (F) Register Extension
     - 1.0
     - optionally enabled based on ``PULP_ZFINX`` parameter

Most content of the RISC-V privileged specification is optional.
CV32E40P currently supports the following features according to the RISC-V Privileged Specification, version 1.11.

* M-Mode
* All CSRs listed in :ref:`cs-registers`
* Hardware Performance Counters as described in :ref:`performance-counters` based on ``NUM_MHPMCOUNTERS`` parameter
* Trap handling supporting direct mode or vectored mode as described at :ref:`exceptions-interrupts`


Synthesis guidelines
--------------------

The CV32E40P core is fully synthesizable.
It has been designed mainly for ASIC designs, but FPGA synthesis
is supported as well.

All the files in the ``rtl`` and ``rtl/include`` folders are synthesizable.
The user should first decide whether to use the flip-flop or latch-based register-file ( see :ref:`register-file`).
Secondly, the user must provide a clock-gating module that instantiates the clock-gating cells of the target technology. This file must have the same interface and module name of the one provided for simulation-only purposes
at ``bhv/cv32e40p_sim_clock_gate.sv`` (see :ref:`clock-gating-cell`).
The  ``rtl/cv32e40p_pmp.sv`` should not be included in the synthesis scripts as it is not supported.
This file is kept in the repository as a starting-point for users that want to implement their own.

The ``constraints/cv32e40p_core.sdc`` file provides an example of synthesis constraints.


ASIC Synthesis
^^^^^^^^^^^^^^

ASIC synthesis is supported for CV32E40P. The whole design is completely
synchronous and uses positive-edge triggered flip-flops, except for the
register file, which can be implemented either with latches or with
flip-flops. See :ref:`register-file` for more details. The
core occupies an area of about 50 kGE when the latch based register file
is used. With the FPU, the area increases to about 90 kGE (30 kGE
FPU, 10 kGE additional register file). A technology specific implementation
of a clock gating cell as described in :ref:`clock-gating-cell` needs to
be provided.

FPGA Synthesis
^^^^^^^^^^^^^^^

FPGA synthesis is supported for CV32E40P when the flip-flop based register
file is used. Since latches are not well supported on FPGAs, it is
crucial to select the flip-flop based register file. The user needs to provide
a technology specific implementation of a clock gating cell as described
in :ref:`clock-gating-cell`.

Verification
------------

The verification environment (testbenches, testcases, etc.) for the CV32E40P
core can be found at  `core-v-verif <https://github.com/openhwgroup/core-v-verif>`_.
It is recommended that you start by reviewing the
`CORE-V Verification Strategy <https://core-v-docs-verif-strat.readthedocs.io/en/latest/>`_.

In early 2021 the CV32E40P achieved Functional RTL Freeze, meaning that is has
been fully verified as per its
`Verification Plan <https://github.com/openhwgroup/core-v-docs/blob/master/verif/CV32E40P/README.md>`_.
The top-level `README in core-v-verif <https://github.com/openhwgroup/core-v-verif#cv32e40p-coverage-data>`_
has a link to the final functional, code and test coverage reports.

The unofficial start date for the CV32E40P verification effort is 2020-02-27,
which is the date the core-v-verif environment "went live".  Between then and
RTL Freeze, a total of 47 RTL issues and 38 User Manual issues were identified
and resolved [1]_.  A breakdown of the RTL issues is as follows:

.. table:: How RTL Issues Were Found
  :name: How RTL Issues Were Found

  +---------------------+-------+----------------------------------------------------+
  | "Found By"          | Count | Note                                               |
  +=====================+=======+====================================================+
  | Simulation          | 18    | See classification below                           |
  +---------------------+-------+----------------------------------------------------+
  | Inspection          | 13    | Human review of the RTL                            |
  +---------------------+-------+----------------------------------------------------+
  | Formal Verification | 13    | This includes both Designer and Verifier use of FV |
  +---------------------+-------+----------------------------------------------------+
  | Lint                |  2    |                                                    |
  +---------------------+-------+----------------------------------------------------+
  | Unknown             |  1    |                                                    |
  +---------------------+-------+----------------------------------------------------+

A classification of the simulation issues by method used to identify them is informative:

.. table:: Breakdown of Issues found by Simulation
  :name: Breakdown of Issues found by Simulation

  +------------------------------+-------+----------------------------------------------------------------------------------------+
  | Simulation Method            | Count | Note                                                                                   |
  +==============================+=======+========================================================================================+
  | Directed, self-checking test | 10    | Many test supplied by Design team and a couple from the Open Source Community at large |
  +------------------------------+-------+----------------------------------------------------------------------------------------+
  | Step & Compare               |  6    | Issues directly attributed to S&C against ISS                                          |
  +------------------------------+-------+----------------------------------------------------------------------------------------+
  | Constrained-Random           |  2    | Test generated by corev-dv (extension of riscv-dv)                                     |
  +------------------------------+-------+----------------------------------------------------------------------------------------+

A classification of the issues themselves:

.. table:: Issue Classification
  :name: Issue Classification

  +------------------------------+-------+----------------------------------------------------------------------------------------+
  | Issue Type                   | Count | Note                                                                                   |
  +==============================+=======+========================================================================================+
  | RTL Functional               | 40    | A bug!                                                                                 |
  +------------------------------+-------+----------------------------------------------------------------------------------------+
  | RTL coding style             |  4    | Linter issues, removing TODOs, removing `ifdefs, etc.                                  |
  +------------------------------+-------+----------------------------------------------------------------------------------------+
  | Non-RTL functional           |  1    | Issue related to behavioral tracer (not part of the core)                              |
  +------------------------------+-------+----------------------------------------------------------------------------------------+
  | Unreproducible               |  1    |                                                                                        |
  +------------------------------+-------+----------------------------------------------------------------------------------------+
  | Invalid                      |  1    |                                                                                        |
  +------------------------------+-------+----------------------------------------------------------------------------------------+

Additional details are available as part of the `CV32E40P v1.0.0 Report <https://github.com/openhwgroup/core-v-docs/tree/master/program/milestones/CV32E40P/RTL_Freeze_v1.0.0>`_.

Contents
--------

 * :ref:`getting-started` discusses the requirements and initial steps to start using CV32E40P.
 * :ref:`core-integration` provides the instantiation template and gives descriptions of the design parameters as well as the input and output ports.
 * :ref:`pipeline-details` described the overal pipeline structure.
 * The instruction and data interfaces of CV32E40P are explained in :ref:`instruction-fetch` and :ref:`load-store-unit`, respectively.
 * The two register-file flavors are described in :ref:`register-file`.
 * :ref:`apu` describes the Auxiliary Processing Unit (APU).
 * :ref:`fpu` describes the Floating Point Unit (FPU).
 * :ref:`sleep_unit` describes the Sleep unit including the PULP Cluster extension.
 * :ref:`hwloop-specs` describes the PULP Hardware Loop extension.
 * The control and status registers are explained in :ref:`cs-registers`.
 * :ref:`performance-counters` gives an overview of the performance monitors and event counters available in CV32E40P.
 * :ref:`exceptions-interrupts` deals with the infrastructure for handling exceptions and interrupts.
 * :ref:`debug-support` gives a brief overview on the debug infrastructure.
 * :ref:`tracer` gives a brief overview of the tracer module.
 * :ref:`custom-isa-extensions` describes the custom instruction set extensions.
 * :ref:`glossary` provides definitions of used terminology.

History
-------

CV32E40P started its life as a fork of the OR10N CPU core based on the OpenRISC ISA. Then, under the name of RI5CY, it became a RISC-V core (2016), and it has been maintained by the PULP platform <https://pulp-platform.org> team until February 2020, when it has been contributed to OpenHW Group https://www.openhwgroup.org>.

As RI5CY has been used in several projects, a list of all the changes made by OpenHW Group since February 2020 follows:

Memory-Protocol
^^^^^^^^^^^^^^^

The Instruction and Data memory interfaces are now compliant with the OBI protocol (see https://github.com/openhwgroup/core-v-docs/blob/master/cores/cv32e40p/OBI-v1.0.pdf).
Such memory interface is slightly different from the one used by RI5CY as: the grant signal can now be kept high by the bus even without the core raising a request; and the request signal does not depend anymore on the rvalid signal (no combinatorial dependency). The OBI is easier to be interfaced to the AMBA AXI and AHB protocols and improves timing as it removes rvalid->req dependency. Also, the protocol forces the address stability. Thus, the core can not retract memory requests once issued, nor can it change the issued address (as was the case for the RI5CY instruction memory interface).

RV32F Extensions
^^^^^^^^^^^^^^^^

The FPU is not instantiated in the core EX stage anymore, and it must be attached to the APU interface.
Previously, RI5CY could select with a parameter whether the FPU was instantiated inside the EX stage or via the APU interface.

RV32A Extensions, Security and Memory Protection
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

CV32E40P core does not support the RV32A (atomic) extensions, the U-mode, and the PMP anymore.
Most of the previous RTL descriptions of these features have been kept but not maintained. The RTL code has been partially kept to allow previous users of these features to develop their own by reusing previously developed RI5CY modules.

CSR Address Re-Mapping
^^^^^^^^^^^^^^^^^^^^^^

CV32E40P is fully compliant with RISC-V.
RI5CY used to have custom performance counters 32b wide (not compliant with RISC-V) in the CSR address space
{0x7A0, 0x7A1, 0x780-0x79F}. CV32E40P is fully compliant with the RISC-V spec.
The custom PULP HWLoop CSRs moved from the 0x7C* to RISC-V user custom space 0x80* address space.

Interrupts
^^^^^^^^^^

RI5CY used to have a req plus a 5bits ID interrupt interface, supporting up to 32 interrupt requests (only one active at a time), with the priority defined outside in an interrupt controller. CV32E40P is now compliant with the CLINT RISC-V spec, extended with 16 custom interrupts lines called fast, for a total of 19 interrupt lines. They can be all active simultaneously, and priority and per-request interrupt enable bit is controlled by the core CLINT definition.

PULP HWLoop Spec
^^^^^^^^^^^^^^^^

RI5CY supported two nested HWLoops. Every loop had a minimum of two instructions. The start and end of the loop addresses
could be misaligned, and the instructions in the loop body could be of any kind. CV32E40P has a more restricted spec for the
HWLoop (see  :ref:`hwloop-specs`).

Compliancy, bug fixing, code clean-up, and documentation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The CV32E40P has been verified. It is fully compliant with RISC-V (RI5CY was partially compliant). Many bugs have been fixed, and the RTL code cleaned-up. The documentation has been formatted with reStructuredText and has been developed following at industrial quality level.



References
----------

1. `Gautschi, Michael, et al. "Near-Threshold RISC-V Core With DSP Extensions for Scalable IoT Endpoint Devices." in IEEE Transactions on Very Large Scale Integration (VLSI) Systems, vol. 25, no. 10, pp. 2700-2713, Oct. 2017 <https://ieeexplore.ieee.org/document/7864441>`_

2. `Schiavone, Pasquale Davide, et al. "Slow and steady wins the race? A comparison of ultra-low-power RISC-V cores for Internet-of-Things applications." 27th International Symposium on Power and Timing Modeling, Optimization and Simulation (PATMOS 2017) <https://doi.org/10.1109/PATMOS.2017.8106976>`_

Contributors
------------

| Andreas Traber
  (`*atraber@iis.ee.ethz.ch* <mailto:atraber@iis.ee.ethz.ch>`__)

Michael Gautschi
(`*gautschi@iis.ee.ethz.ch* <mailto:gautschi@iis.ee.ethz.ch>`__)

Pasquale Davide Schiavone
(`*pschiavo@iis.ee.ethz.ch* <mailto:pschiavo@iis.ee.ethz.ch>`__)

Arjan Bink (`*arjan.bink@silabs.com* <mailto:arjan.bink@silabs.com>`__)

Paul Zavalney (`*paul.zavalney@silabs.com* <mailto:paul.zavalney@silabs.com>`__)

| Micrel Lab and Multitherman Lab
| University of Bologna, Italy

| Integrated Systems Lab
| ETH Zürich, Switzerland


.. [1]
   It is a testament on the quality of the work done by the PULP platform team
   that it took a team of professonal verification engineers more than 9 months
   to find all these issues.
