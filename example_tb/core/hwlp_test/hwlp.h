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

/*

HW-Loop realted macros for testing cv32e40p

HW-Loops must start with the first instruction 4-B aligned
HW-Loops cannot contain Jumps/Branches
HW-Loops cannot contain compressed instructions
The last instruction of HW-Loop 1 and the last instruction of HW-Loop 0 must be separated
by at least another instruction

*/

// Syntax:
// lp.setupi L, uimmS, uimmL
// L = x0, x1
// uimmS = n_times
// uimmL = 4*n_instructions

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

// HWLP for interrupts bombing:
// Interrupts modifies the stack! Offset: -80 should be enough to stay safe
// Expect RES_EXPECTED as result
#define HWLP_TEST_INTERRUPT0(res) asm volatile ("addi t0, x0, 6\n\t\
                                                sw t0, -64(sp)\n\t\
                                                addi t2, x0, 53\n\t\
                                                sw t2, -68(sp)\n\t\
                                                lp.setupi x1, 40, 24\n\t\
                                                lp.setupi x0, 40, 12\n\t\
                                                addi t2, t2, 1\n\t\
                                                addi t2, t2, 2\n\t\
                                                addi t2, t2, 3\n\t\
                                                addi t2, t2, 13\n\t\
                                                addi t2, t2, 9\n\t\
                                                sw t2, -80(sp)\n\t\
                                                lp.setupi x1, 40, 24\n\t\
                                                lp.setupi x0, 40, 12\n\t\
                                                lw t1, -80(sp)\n\t\
                                                addi t2, t1, 1\n\t\
                                                sw t2, -80(sp)\n\t\
                                                addi t2, t2, 15\n\t\
                                                sw t2, -80(sp)\n\t\
                                                mv %0, t2"\
                                                : "=r" (res) : : "t0", "t2", "t1")

// t2 = 53 + 6*40*40 + 22*40 + 1*40*40 + 15*40 = 12733
#define RES_EXPECTED0 12733

// HWLP for interrupts bombing, with CSR operations (both at END and END-4):
// mcountinhibit inhibits mcycle after reset
// We can use mcycle for writing/reading
// We write a partial value into mcycle, then read it for multiple times
// Expect RES_EXPECTED as result
#define HWLP_TEST_INTERRUPT1(res) asm volatile ("addi t0, x0, 6\n\t\
                                                sw t0, -64(sp)\n\t\
                                                addi t2, x0, 53\n\t\
                                                sw t2, -68(sp)\n\t\
                                                addi t0, x0, 7\n\t\
                                                lp.setupi x1, 40, 40\n\t\
                                                lp.setupi x0, 40, 28\n\t\
                                                addi t2, t2, 1\n\t\
                                                addi t2, t2, 2\n\t\
                                                addi t2, t2, 3\n\t\
                                                csrrw t2, mcycle, t2\n\t\
                                                addi t1, x0, 0\n\t\
                                                csrrw t1, mcycle, t1\n\t\
                                                mv t2, t1\n\t\
                                                addi t2, t2, 13\n\t\
                                                addi t2, t2, 9\n\t\
                                                sw t2, -80(sp)\n\t\
                                                lp.setupi x1, 40, 44\n\t\
                                                lp.setupi x0, 40, 32\n\t\
                                                lw t1, -80(sp)\n\t\
                                                addi t2, t1, 1\n\t\
                                                csrrw t2, mcycle, t2\n\t\
                                                addi t1, x0, 0\n\t\
                                                csrrw t1, mcycle, t1\n\t\
                                                mv t2, t1\n\t\
                                                sw t2, -80(sp)\n\t\
                                                csrrw t1, mcycle, t1\n\t\
                                                addi t2, t2, 15\n\t\
                                                sw t2, -80(sp)\n\t\
                                                mv %0, t2"\
                                                : "=r" (res) : : "t0", "t2", "t1")

// t2 = 53 + 6*40*40 + 22*40 + 1*40*40 + 15*40 = 12733
#define RES_EXPECTED1 12733

// HWLP for interrupts bombing, with an illegal instruction inside the loop (HWLP_END-4):
// The first time dret is met, the core should jump to the handler
// Expect RES_EXPECTED as result
#define HWLP_TEST_INTERRUPT2(res) asm volatile ("addi t0, x0, 6\n\t\
                                                sw t0, -64(sp)\n\t\
                                                addi t2, x0, 53\n\t\
                                                sw t2, -68(sp)\n\t\
                                                addi t1, x0, 7\n\t\
                                                lp.setupi x1, 10, 28\n\t\
                                                lp.setupi x0, 10, 16\n\t\
                                                addi t2, t2, 1\n\t\
                                                addi t2, t2, 2\n\t\
                                                dret\n\t\
                                                addi t2, t2, 3\n\t\
                                                addi t2, t2, 13\n\t\
                                                addi t2, t2, 9\n\t\
                                                sw t2, -80(sp)\n\t\
                                                lp.setupi x1, 10, 24\n\t\
                                                lp.setupi x0, 10, 12\n\t\
                                                lw t1, -80(sp)\n\t\
                                                addi t2, t1, 1\n\t\
                                                sw t2, -80(sp)\n\t\
                                                addi t2, t2, 15\n\t\
                                                sw t2, -80(sp)\n\t\
                                                mv %0, t2"\
                                                : "=r" (res) : : "t0", "t2", "t1")

// t2 = 53 + 6*10*10 + 22*10 + 1*10*10 + 15*10 = 1123
#define RES_EXPECTED2 1123

// HWLP for interrupts bombing, with an illegal instruction inside the loop (HWLP_END):
// The first time dret is met, the core should jump to the handler
// Do not expect anything certain, as the last instruction of the HWLP is illegal.
// After having jumped to the handler, the mret returns HWLP_END+4 so it exit the HWLP.
#define HWLP_TEST_INTERRUPT3(res) asm volatile ("addi t0, x0, 6\n\t\
                                                sw t0, -64(sp)\n\t\
                                                addi t2, x0, 53\n\t\
                                                sw t2, -68(sp)\n\t\
                                                addi t1, x0, 7\n\t\
                                                lp.setupi x1, 40, 28\n\t\
                                                lp.setupi x0, 40, 16\n\t\
                                                addi t2, t2, 1\n\t\
                                                addi t2, t2, 2\n\t\
                                                addi t2, t2, 3\n\t\
                                                dret\n\t\
                                                addi t2, t2, 13\n\t\
                                                addi t2, t2, 9\n\t\
                                                sw t2, -80(sp)\n\t\
                                                lp.setupi x1, 40, 24\n\t\
                                                lp.setupi x0, 40, 12\n\t\
                                                lw t1, -80(sp)\n\t\
                                                addi t2, t1, 1\n\t\
                                                sw t2, -80(sp)\n\t\
                                                addi t2, t2, 15\n\t\
                                                sw t2, -80(sp)\n\t\
                                                mv %0, t2"\
                                                : "=r" (res) : : "t0", "t2", "t1")


// HWLP for interrupts bombing, with a divison instruction to cause a stall (HWLP_END+4 and HWLP_END):
// Memory operations at HWLP_END+4 and HWLP_END
// The initial value t2 is kept constant inside each HWLP
#define HWLP_TEST_INTERRUPT4(res) asm volatile ("addi t0, x0, 3\n\t\
                                                sw t0, -80(sp)\n\t\
                                                addi t0, x0, 85\n\t\
                                                sw t0, -84(sp)\n\t\
                                                addi t2, x0, 53\n\t\
                                                sw t2, -68(sp)\n\t\
                                                addi t1, x0, 3\n\t\
                                                lp.setupi x1, 40, 40\n\t\
                                                lp.setupi x0, 40, 16\n\t\
                                                addi t0, t2, 21\n\t\
                                                addi t0, t0, 10\n\t\
                                                addi t2, t0, 75\n\t\
                                                div t2, t2, t1\n\t\
                                                addi t1, x0, 5\n\t\
                                                addi t0, t2, 41\n\t\
                                                addi t2, t0, 171\n\t\
                                                div t2, t2, t1\n\t\
                                                addi t1, x0, 3\n\t\
                                                lp.setupi x1, 40, 44\n\t\
                                                lp.setupi x0, 40, 20\n\t\
                                                addi t2, t2, 21\n\t\
                                                lw t1, -84(sp)\n\t\
                                                add t2, t1, t1\n\t\
                                                lw t1, -80(sp)\n\t\
                                                div t2, t2, t1\n\t\
                                                addi t1, x0, 5\n\t\
                                                addi t0, t2, 41\n\t\
                                                addi t2, t0, 171\n\t\
                                                div t2, t2, t1\n\t\
                                                lw t1, -80(sp)\n\t\
                                                mv %0, t2"\
                                                : "=r" (res) : : "t0", "t2", "t1")

// (53 + 2*53) / 3 LOOPED
// (53 + 4*53) / 5 LOOPED
#define RES_EXPECTED4 53
