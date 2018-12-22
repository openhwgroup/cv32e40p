RI5CY Core Testbench
=====================
This testbench runs
[riscv-tests](https://github.com/riscv/riscv-tests/tree/master/isa)(rv32ui,
rv32uc) and
[riscv-compliance-tests](https://github.com/riscv/riscv-compliance)(rv32i) on
RI5CY in a minimalistic setting. It contains a RAM model and a small pseudo
peripheral that dumps any writes to `0x1000_0000` to stdout. The small tests
signal success or failure by writing `12345679` or `1` respectively to
`0x2000_0000`. Only `vsim` was tested as simulator.

Running the testbench
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain.
Call `make firmware-run` to build the testbench and the firmware, and run it.
Use `VSIM_FLAGS` to configure the simulator e.g. `make firmware-run
VSIM_FLAGS="-gui -debugdb"`.

Options
----------------------
A few plusarg options are supported.
* `+verbose` to show all memory read and writes and other miscellaneous information.
* `+vcd` to produce a vcd file called `riscy_tb.vcd`.
* `+firmware=path_to_firmware` to load a specific firmware. It is a bit tricky to
build and link your own program. Have a look at `picorv_firmware/start.S` and
`picorv_firmware/link.ld` for more insight.

Examples
-----------------------
Run all riscv-tests to completion and produce a vcd dump:
`make firmware-run VSIM_FLAGS=+vcd`