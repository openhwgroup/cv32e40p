# RTL source Lint

This folder contains LINT scripts that runs using SiemensEDA Questa AutoCheck tool. It requires SiemensEDA QuestaSim to first compile the design.

Those scripts allow to check RTL coding quality using common guidelines and rules. It can find syntax errors or issues leading to bad/incorrect synthesis (like latches in combinational process).
Common practice is to launch LINT check prior to committing RTL sources to git repository.

As cv32e40p\_top has 5 parameters and to be able to check different parameters values, a new top level module (cv32e40p\_wrapper) has been created together with some predefined configuration packages (in config\_?p\_?f\_?z\_?lat\_??c directories).

Configuration directory naming style is:
- \_?p : PULP enabled or not (0 or 1)
- \_?f : FPU enabled or not (0 or 1)
- \_?z : ZFINX enabled or not (0 or 1)
- \_?lat : FPU instructions latency (0, 1 or 2)
- \_?c : PULP\_CLUSTER enabled or not (0 or 1)

### Running the script

From a shell, please execute:

```
./lint.sh 1p_0f_0z_0lat_0c
```

The script uses `../../rtl` as design sources to check.

Intermediate logs are visible in `questa_autocheck/config_?p_?f_?z_?lat_?c` and `questa_autocheck/config_?p_?f_?z_?lat_?c/formal_lint_out` and final lint report in `questa_autocheck/config_?p_?f_?z_?lat_?c/formal_lint.rpt`

