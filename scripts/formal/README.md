## CV32E40P Formal

 This folder contains the source and scripts used in the effort to justify waived code coverage holes using formal tools.

 Disclaimer: This has been developped and tested with Siemens Questa formal and the Makefile only support this tool. Porting to other tools should be straightforward as all source files are standard sva.

### Introduction
 To assist code coverage analysis we formally proved that some code was in our case unreachable. Each assertion correspond to one coverage holes. We tried to keep the constraints as minimal as possible. The only constraints we are using are:
 - OBI protocol constraints on both instructions and data interfaces
 - Disabling scan


### How to use

Inside this folder, with ```vlog``` and ```qverify``` available in your PATH, run one of the following command.

| Command         | Description                                   |
|-----------------|-----------------------------------------------|
|make run         | Run default config (no corev_pulp, no FPU)    |
|make run_pulp    | Run config corev_pulp withou FPU              |
|make run_pulp_F0 | Run config corev_pulp with FPU with latency 0 |
|make clean       | Remove all temporary file                     |

All runs are in batch. At the end of the run, use ```qverify <PATH_TO_PROPCHECK_DB>``` to open the results in GUI.