/*
 * Copyright 2020 ETH Zurich
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

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
