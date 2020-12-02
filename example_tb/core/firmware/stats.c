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

#include "firmware.h"

static void stats_print_dec(unsigned int val, int digits, bool zero_pad)
{
    char buffer[32];
    char *p = buffer;
    while (val || digits > 0) {
	if (val)
	    *(p++) = '0' + val % 10;
	else
	    *(p++) = zero_pad ? '0' : ' ';
	val = val / 10;
	digits--;
    }
    while (p != buffer) {
	if (p[-1] == ' ' && p[-2] == ' ')
	    p[-1] = '.';
	print_chr(*(--p));
    }
}

void init_stats(void)
{
    unsigned int zero = 0; 
    unsigned int enable = 0xfffffff8; /* cycles and instr count enable */
    __asm__ volatile("csrw 0xb00, %0" ::"r"(zero));
    __asm__ volatile("csrw 0xb02, %0" ::"r"(zero));
    __asm__ volatile("csrw 0x320, %0" ::"r"(enable));
}

void stats(void)
{
    unsigned int num_cycles, num_instr;
    __asm__ volatile("csrr %0, 0xb00" : "=r"(num_cycles));
    __asm__ volatile("csrr %0, 0xb02" : "=r"(num_instr));
    print_str("Cycle counter ........");
    stats_print_dec(num_cycles, 8, false);
    print_str("\nInstruction counter ..");
    stats_print_dec(num_instr, 8, false);
    print_str("\nCPI: ");
    stats_print_dec((num_cycles / num_instr), 0, false);
    print_str(".");
    stats_print_dec(((100 * num_cycles) / num_instr) % 100, 2, true);
    print_str("\n");
}
