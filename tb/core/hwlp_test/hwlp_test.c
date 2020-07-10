#include <stdio.h>
#include <stdlib.h>
#include "mem_stall.h"
#include "hwlp.h"

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
