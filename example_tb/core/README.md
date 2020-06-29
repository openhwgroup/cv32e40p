Example testbench
----------------------
This is an example testbench that provides an example of running 'Hello World'. The
actual testbench and verification environment for CV32E40P can be found in
https://github.com/openhwgroup/core-v-verif

Supported Compilers
----------------------
Note that this testbench requires either the upstream
[riscv-gcc](https://github.com/riscv/riscv-gcc) or if you want to use our custom
PULP instructions our PULP
[riscv-gcc](https://github.com/pulp-platform/pulp-riscv-gcc) (recommended to be
installed through our [sdk](https://github.com/pulp-platform/pulp-sdk)).

Running your own programs
---------------------
The `custom` folder has an example on a hello world program that can be run with
the testbench. The relevant sections in the Makefile on how to compile and link
this program can be found under `Running custom programs`. In order to compile
it successfully you need gcc with RISC-V support and a fitting newlib installed.
It is strongly recommended you use the [RISC-V GNU
Toolchain](https://github.com/riscv/riscv-gnu-toolchain) for that (follow the
`Installation (Newlib)` section) and point your `RISCV` environment variable to
it.

We have prepared a 'Hello World' program which you can run in the testbench. It
demonstrates how you can run your own programs. Call `custom-vsim-run`  to
run it with `vsim`.

Running the testbench with vsim
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain. Call `make
firmware-vsim-run` to build the testbench and the firmware, and run it. Use
`VSIM_FLAGS` to configure the simulator e.g. `make custom-vsim-run
VSIM_FLAGS="-gui -debugdb"`.

Running with other simulators
----------------------
Other simulator and more extensive test cases are supported in https://github.com/openhwgroup/core-v-verif

Options
----------------------
A few plusarg options are supported.
* `+verbose` to show all memory read and writes and other miscellaneous information.

* `+vcd` to produce a vcd file called `riscy_tb.vcd`. Verilator always produces
  a vcd file called `verilator_tb.vcd`.

Examples
-----------------------
Run all riscv-tests to completion and produce a vcd dump:
`make firmware-vsim-run VSIM_FLAGS=+vcd`
