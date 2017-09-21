RI5CY Verilator Model
=====================

The Verilator model of RI5CY instantiates the RI5CY core along with a RAM. A
testbench accompanies the model, to demonstrate the use of the Verilated model.

Building the model
------------------

In order to build the model, you will require a recent version of Verilator
(3.906 or above), and that version of verilator must be known to pkg-config.

Run `make` in the `verilator-model` directory to build the model.

The Testbench
-------------

The testbench demonstrates:

- Instantiating the model
- Writing data to memory (a short program)
- Resetting the CPU
- Running the CPU
- Using the debug unit to halt, set traps on exceptions, single-step, and
  resume.

The testbench can be executed as `./testbench`. The expected output of the
testbench is:

```
About to halt and set traps on exceptions
About to resume
Cycling clock to run for a few instructions
Halting
Halted. Setting single step
DBG_CTRL  10001
DBG_HIT   0
DBG_CAUSE 1f
DBG_NPC   cc
DBG_PPC   c8
About to do one single step
DBG_CTRL  10001
DBG_HIT   1
DBG_CAUSE 0
DBG_NPC   d0
DBG_PPC   cc
About to do one single step
DBG_CTRL  10001
DBG_HIT   1
DBG_CAUSE 0
DBG_NPC   d4
DBG_PPC   d0
About to do one single step
DBG_CTRL  10001
DBG_HIT   1
DBG_CAUSE 0
DBG_NPC   d8
DBG_PPC   d4
About to do one single step
DBG_CTRL  10001
DBG_HIT   1
DBG_CAUSE 0
DBG_NPC   dc
DBG_PPC   d8
About to do one single step
```
