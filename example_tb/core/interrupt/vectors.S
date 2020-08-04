/*
* Copyright 2019 ETH Zürich and University of Bologna
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
*/

.section .vectors, "ax"
.option norvc

/* Needed to declare IRQ routine */
.global timer_irq_handler
.global software_irq_handler
.global external_irq_handler
.global fast0_irq_handler
.global fast1_irq_handler
.global fast2_irq_handler
.global fast3_irq_handler
.global fast4_irq_handler
.global fast5_irq_handler
.global fast6_irq_handler
.global fast7_irq_handler
.global fast8_irq_handler
.global fast9_irq_handler
.global fast10_irq_handler
.global fast11_irq_handler
.global fast12_irq_handler
.global fast13_irq_handler
.global fast14_irq_handler
.global fast15_irq_handler

vector_table:
	j sw_irq_handler               /*  0                          */
	j verification_irq_handler     /*  1                          */
	j __no_irq_handler             /*  2                          */
	j software_irq_handler         /*  3 EXC_CAUSE_IRQ_SOFTWARE_M */
	j __no_irq_handler             /*  4                          */
	j __no_irq_handler             /*  5                          */
	j __no_irq_handler             /*  6                          */
	j timer_irq_handler            /*  7 EXC_CAUSE_IRQ_TIMER_M    */
	j __no_irq_handler             /*  8                          */
	j __no_irq_handler             /*  9                          */
	j __no_irq_handler             /* 10                          */
	j external_irq_handler         /* 11 EXC_CAUSE_IRQ_EXTERNAL_M */
	j __no_irq_handler             /* 12                          */
	j __no_irq_handler             /* 13                          */
	j __no_irq_handler             /* 14                          */
	j __no_irq_handler             /* 15                          */
	j fast0_irq_handler            /* 16 EXC_CAUSE_IRQ_FAST_0     */
	j fast1_irq_handler            /* 17 EXC_CAUSE_IRQ_FAST_1     */
	j fast2_irq_handler            /* 18 EXC_CAUSE_IRQ_FAST_2     */
	j fast3_irq_handler            /* 19 EXC_CAUSE_IRQ_FAST_3     */
	j fast4_irq_handler            /* 20 EXC_CAUSE_IRQ_FAST_4     */
	j fast5_irq_handler            /* 21 EXC_CAUSE_IRQ_FAST_5     */
	j fast6_irq_handler            /* 22 EXC_CAUSE_IRQ_FAST_6     */
	j fast7_irq_handler            /* 23 EXC_CAUSE_IRQ_FAST_7     */
	j fast8_irq_handler            /* 24 EXC_CAUSE_IRQ_FAST_8     */
	j fast9_irq_handler            /* 25 EXC_CAUSE_IRQ_FAST_9     */
	j fast10_irq_handler           /* 26 EXC_CAUSE_IRQ_FAST_10    */
	j fast11_irq_handler           /* 27 EXC_CAUSE_IRQ_FAST_11    */
	j fast12_irq_handler           /* 28 EXC_CAUSE_IRQ_FAST_12    */
	j fast13_irq_handler           /* 29 EXC_CAUSE_IRQ_FAST_13    */
	j fast14_irq_handler           /* 30 EXC_CAUSE_IRQ_FAST_14    */
	j fast15_irq_handler           /* 31 EXC_CAUSE_IRQ_FAST_15    */

.section .text.vecs
/* exception handling */
__no_irq_handler:
	la a0, no_exception_handler_msg
	jal ra, puts
	j __no_irq_handler


sw_irq_handler:
	csrr t0, mcause
	slli t0, t0, 1  /* shift off the high bit */
	srli t0, t0, 1
	li t1, 2
	beq t0, t1, handle_illegal_insn
	li t1, 11
	beq t0, t1, handle_ecall
	li t1, 3
	beq t0, t1, handle_ebreak
	j handle_unknown

/* when we get a timeout*/
/* timer_irq_handler:
	la a0, timeout_msg
	jal ra, print_str*/



handle_ecall:
	la a0, ecall_msg
	jal ra, puts
	j end_handler

handle_ebreak:
	la a0, ebreak_msg
	jal ra, puts
	j end_handler

handle_illegal_insn:
	la a0, illegal_insn_msg
	jal ra, puts
	j end_handler

handle_unknown:
	la a0, unknown_msg
	jal ra, puts
	j end_handler

end_handler:
	csrr a0, mepc
	addi a0, a0, 4
	csrw mepc, a0
	mret
/* this interrupt can be generated for verification purposes, random or when the PC is equal to a given value*/
verification_irq_handler:
	mret

.section .rodata
illegal_insn_msg:
	.string "illegal instruction exception handler entered\n"
ecall_msg:
	.string "ecall exception handler entered\n"
ebreak_msg:
	.string "ebreak exception handler entered\n"
unknown_msg:
	.string "unknown exception handler entered\n"
no_exception_handler_msg:
	.string "no exception handler installed\n"
timeout_msg:
	.string "\n\nTEST TIMEOUT...\n\n"
