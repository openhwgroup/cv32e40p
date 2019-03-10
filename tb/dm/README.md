RI5CY Core plus Debug Unit Testbench
=====================

This testbench tests RI5CY together with a v0.13.1 compliant [debug
unit](https://www.github.com/pulp-platform/riscv-dbg). There are several tests
that can be run, but for now it is just `riscv test_compliance` of
[riscv-openocd](https://www.github.com/riscv/riscv-openocd) (see in
`pulpissimo.cfg`) and a not yet scripted run of gdb connecting to openocd,
loading and running a hello world program (see `prog/test.c`).

Setup
----------------------

Point you environment variable `RISCV` to your RISC-V toolchain. Call `make
prog-run` to build the testbench and the program, and run it. Use `VSIM_FLAGS`
to configure the simulator e.g. `make prog-run VSIM_FLAGS="-gui -debugdb"`.

You need `riscv-openocd`.

Running the testbench with [verilator](https://www.veripool.org/wiki/verilator)
is not supported yet.


Run Openocd Test
-----------------------
1. `make prog-run`
3. (in new terminal) `export JTAG_VPI_PORT=port_name_from 1.`
2. (in new terminal) `openocd -f pulpissimo.cfg`
