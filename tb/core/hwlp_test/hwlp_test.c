#include <stdio.h>
#include <stdlib.h>
#include "mem_stall.h"

// lp.setupi L, uimmS, uimmL // L = x0, x1 | uimmS = n_times | uimmL = 4*n_instructions

// Simple loop
#define HWLP_TEST0 asm volatile ("lp.setupi x1, 10, 16\n\t\
                                  addi t1, t1, 1\n\t\
                                  addi t1, t1, 2\n\t\
                                  addi t1, t1, 3\n\t\
                                  addi t2, t2, 4\n\t\
                                  mul t1, t1, t2" \
                                 : : : "t1", "t2")

// Nested loops
#define HWLP_TEST1 asm volatile ("lp.setupi x1, 10, 44\n\t\
                                  addi t1, t1, 1\n\t\
                                  addi t2, t1, 2\n\t\
                                  addi t1, t2, 3\n\t\
                                  addi t2, t2, 4\n\t\
                                  lp.setupi x0, 20, 12\n\t\
                                  addi t1, t1, 5\n\t\
                                  addi t2, t1, 6\n\t\
                                  addi t1, t2, 7\n\t\
                                  addi t2, t2, 8\n\t\
                                  addi t2, t2, 9\n\t\
                                  addi t2, t2, 10\n\t\
                                  mul t2, t1, t1" \
                                  : : : "t1", "t2")

// Big nested loops
#define HWLP_TEST2 asm volatile ("lp.setupi x1, 100, 44\n\t\
                                  addi t1, t1, 1\n\t\
                                  addi t2, t1, 2\n\t\
                                  addi t1, t2, 3\n\t\
                                  addi t2, t2, 4\n\t\
                                  lp.setupi x0, 200, 12\n\t\
                                  addi t1, t1, 5\n\t\
                                  addi t2, t1, 6\n\t\
                                  addi t1, t2, 7\n\t\
                                  addi t2, t2, 8\n\t\
                                  addi t2, t2, 9\n\t\
                                  addi t2, t2, 10\n\t\
                                  mul t2, t1, t1" \
                                  : : : "t1", "t2")

// Random memory operations inside the loop
#define HWLP_TEST3 asm volatile ("addi t1,x0,0\n\t\
                                  addi t2,x0,0\n\t\
                                  lp.setupi x1, 102, 60\n\t\
                                  addi t1, x0, 4\n\t\
                                  addi t2, x0, 8\n\t\
                                  lw t1, 24(t2)\n\t\
                                  addi t2, x0, 12\n\t\
                                  addi t1, x0, 4\n\t\
                                  lp.setupi x0, 21, 20\n\t\
                                  addi t2, x0, 4\n\t\
                                  addi t1, x0, 4\n\t\
                                  lw t2, 8(t1)\n\t\
                                  addi t2, x0, 4\n\t\
                                  addi t2, x0, 4\n\t\
                                  addi t2, x0, 4\n\t\
                                  lw t1, 0(t2)\n\t\
                                  sw t2, -4(sp)\n\t\
                                  addi t2, x0, 4\n\t\
                                  addi t2, x0, 4\n\t\
                                  lw t2, 8(t2)\n\t\
                                  addi t2, x0, 4\n\t\
                                  addi t2, x0, 4\n\t\
                                  sw t2, -12(sp)\n\t\
                                  addi t2, x0, 8\n\t\
                                  addi t1, x0, 12\n\t\
                                  lw t2, 4(t1)" \
                                  : : : "t0", "t1", "t2")

// Minimum size nested HWLPs
#define HWLP_TEST4 asm volatile ("addi t0, x0, 0\n\t\
                                  lp.setup x1, t0, 24\n\t\
                                  lp.setupi x0, 21, 12\n\t\
                                  addi t2, x0, 1\n\t\
                                  addi t1, x0, 2\n\t\
                                  lw t2, 24(t0)\n\t\
                                  add t1, x0, t2\n\t\
                                  sw t1, -28(sp)\n\t\
                                  mul t0, t0, t0" \
                                  : : : "t0", "t1", "t2")

// Mixed operations and HWLP instructions.
// Extreme cases allowed by documentation:
// - (HWLoop[1].endaddress = HWLoop[0].endaddress + 8)
// - (Minimum size nested HWLP)
#define HWLP_TEST5 asm volatile ("addi t0,x0,0\n\t\
                                  addi t1,x0,0\n\t\
                                  addi t2,x0,0\n\t\
                                  lp.starti x1,16\n\t\
                                  lp.counti x1,12\n\t\
                                  lp.endi x1,100\n\t\
                                  lp.starti x0,52\n\t\
                                  addi t0,x0,100\n\t\
                                  lp.count x0,t0\n\t\
                                  lp.endi x0,76\n\t\
                                  addi t0, x0, 1024\n\t\
                                  addi t1, x0, 4\n\t\
                                  addi t2, x0, 8\n\t\
                                  add t1, t2, t2\n\t\
                                  mul t2, t0, t1\n\t\
                                  lw t2, 128(t0)\n\t\
                                  sw t2, -8(sp)\n\t\
                                  lw t2, 256(t0)\n\t\
                                  addi t2, x0, 4\n\t\
                                  lw t1, 0(t0)\n\t\
                                  lw t1, 4(t0)\n\t\
                                  lw t2, 8(t0)\n\t\
                                  lw t1, 12(t0)\n\t\
                                  lw t2, 16(t0)\n\t\
                                  sw t1, -20(sp)\n\t\
                                  sw t2, -24(sp)\n\t\
                                  sw t1, -28(sp)\n\t\
                                  lw t1, 32(t0)\n\t\
                                  sw t2, -36(sp)\n\t\
                                  lw t1, 0(t0)\n\t\
                                  sw t2, -4(sp)\n\t\
                                  lw t2, 8(t0)\n\t\
                                  addi t2, x0, 4\n\t\
                                  addi t2, x0, 4\n\t\
                                  sw t2, -12(sp)\n\t\
                                  addi t1, x0, 28\n\t\
                                  lp.setup x1, t0, 24\n\t\
                                  lp.setupi x0, 21, 12\n\t\
                                  addi t2, x0, 8\n\t\
                                  addi t1, x0, 12\n\t\
                                  sw t2, -24(sp)\n\t\
                                  addi t1, x0, 12\n\t\
                                  sw t1, -28(sp)\n\t\
                                  lw t1, 32(t0)\n\t\
                                  addi t2, x0, 8\n\t\
                                  addi t1, x0, 12\n\t\
                                  lw t2, 4(t0)" \
                                  : : : "t0", "t1", "t2")

// HWLP with DIV and MEM ops
#define HWLP_TEST6 asm volatile ("addi t0, x0, 0\n\t\
                                  lp.setupi x1, 10, 24\n\t\
                                  lp.setupi x0, 20, 12\n\t\
                                  addi t2, x0, 1381\n\t\
                                  addi t1, x0, 17\n\t\
                                  div t2, t2, t1\n\t\
                                  lw t2, 24(t0)\n\t\
                                  div t1, t1, t2\n\t\
                                  sw t1, -28(sp)\n\t\
                                  mul t0, t0, t0" \
                                  : : : "t0", "t1", "t2")

int main(int argc, char *argv[])
{
#ifdef RANDOM_MEM_STALL
    activate_random_stall();
#endif

    asm volatile("ecall" : : : "ra");
    HWLP_TEST0;
    asm volatile("ebreak" : : : "ra");
    HWLP_TEST1;
    asm volatile("ecall" : : : "ra");
    HWLP_TEST2;
    asm volatile("ebreak" : : : "ra");
    asm volatile("fence.i" : : : "ra");
    asm volatile("ebreak" : : : "ra");
    HWLP_TEST3;
    asm volatile("ecall" : : : "ra");
    asm volatile("ecall" : : : "ra");
    HWLP_TEST4;
    asm volatile("ecall" : : : "ra");
    HWLP_TEST5;
    asm volatile("fence.i" : : : "ra");
    HWLP_TEST6;

    return EXIT_SUCCESS;
}
