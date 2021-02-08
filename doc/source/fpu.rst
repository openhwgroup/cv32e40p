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

.. _fpu:

Floating Point Unit (FPU)
=========================

The RV32F ISA extension for floating-point support in the form of IEEE-754 single
precision can be enabled by setting the parameter **FPU** of the toplevel file
``cv32e40p_core.sv`` to 1. This will extend the CV32E40P decoder accordingly.
The actual Floating Point Unit (FPU) is instantiated outside the
CV32E40P and is accessed via the APU interface (see :ref:`apu`).
The FPU repository used by the CV32E40P core is available at
https://github.com/pulp-platform/fpnew.
In the core repository, a wrapper showing how the FPU is connected
to the core is available at ``example_tb/core/cv32e40p_fp_wrapper.sv``.
By default a dedicated register file consisting of 32
floating-point registers, ``f0``-``f31``, is instantiated. This default behavior
can be overruled by setting the parameter **PULP_ZFINX** of the toplevel
file ``cv32e40p_core.sv`` to 1, in which case the dedicated register file is
not included and the general purpose register file is used instead to
host the floating-point operands.

The latency of the individual instructions are set by means of parameters in the
FPU repository (see https://github.com/pulp-platform/fpnew/tree/develop/docs).


FP CSR
------

When using floating-point extensions the standard specifies a
floating-point status and control register (:ref:`csr-fcsr`) which contains the
exceptions that occurred since it was last reset and the rounding mode.
:ref:`csr-fflags` and :ref:`csr-frm` can be accessed directly or via :ref:`csr-fcsr` which is mapped to
those two registers.
