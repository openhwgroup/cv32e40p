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
#include <time.h>

#include "isr.h"
#include "matrix.h"
#include "mem_stall.h"

#define ERR_CODE_TEST_2      2
#define ERR_CODE_TEST_3      3
#define ERR_CODE_TEST_5      5

#define OUTPORT 0x10000000

#define RND_STALL_REG_10       0x16000028 // irq_mode
#define RND_STALL_REG_11       0x1600002C // irq_min_cycles
#define RND_STALL_REG_12       0x16000030 // irq_max_cycles
#define RND_STALL_REG_13       0x16000034 // irq_pc_trig
#define RND_STALL_REG_14       0x16000038 // irq_lines

#define IRQ_MODE_STD     1
#define IRQ_MODE_RND     2
#define IRQ_MODE_PC_TRIG 3
#define IRQ_MODE_SD      4

#define MSTATUS_MIE_BIT 3

#define IRQ_NUM 19
#define STD_IRQ_MASK 0xFFFF0888 // this accounts for non implemented irqs

#define SOFTWARE_IRQ_ID  3
#define TIMER_IRQ_ID     7
#define EXTERNAL_IRQ_ID  11
#define FAST0_IRQ_ID     16
#define FAST1_IRQ_ID     17
#define FAST2_IRQ_ID     18
#define FAST3_IRQ_ID     19
#define FAST4_IRQ_ID     20
#define FAST5_IRQ_ID     21
#define FAST6_IRQ_ID     22
#define FAST7_IRQ_ID     23
#define FAST8_IRQ_ID     24
#define FAST9_IRQ_ID     25
#define FAST10_IRQ_ID    26
#define FAST11_IRQ_ID    27
#define FAST12_IRQ_ID    28
#define FAST13_IRQ_ID    29
#define FAST14_IRQ_ID    30
#define FAST15_IRQ_ID    31

#define RND_IRQ_NUM        50
#define RND_IE_NUM         50
#define RND_IRQ_MIN_CYCLES 100
#define RND_IRQ_MAX_CYCLES 200

volatile uint32_t irq_processed           = 1;
volatile uint32_t irq_id                  = 0;
volatile uint64_t irq_pending             = 0;
volatile uint32_t irq_pending32_std       = 0;
volatile uint32_t irq_to_test32_std       = 0;
volatile uint64_t prev_irq_pending        = 0;
volatile uint32_t prev_irq_pending32_std  = 0;
volatile uint32_t first_irq_pending32_std = 0;
volatile uint32_t ie_mask32_std           = 0;
volatile uint32_t mmstatus                = 0;
volatile uint32_t bit_to_set              = 0;
volatile uint32_t irq_mode                = 0;

uint32_t IRQ_ID_PRIORITY [IRQ_NUM] =
{
    FAST15_IRQ_ID   ,
    FAST14_IRQ_ID   ,
    FAST13_IRQ_ID   ,
    FAST12_IRQ_ID   ,
    FAST11_IRQ_ID   ,
    FAST10_IRQ_ID   ,
    FAST9_IRQ_ID    ,
    FAST8_IRQ_ID    ,
    FAST7_IRQ_ID    ,
    FAST6_IRQ_ID    ,
    FAST5_IRQ_ID    ,
    FAST4_IRQ_ID    ,
    FAST3_IRQ_ID    ,
    FAST2_IRQ_ID    ,
    FAST1_IRQ_ID    ,
    FAST0_IRQ_ID    ,
    EXTERNAL_IRQ_ID ,
    SOFTWARE_IRQ_ID ,
    TIMER_IRQ_ID
};


// macro to print out a variable as binary
#define PRINTF_BINARY_PATTERN_INT8 "%c%c%c%c%c%c%c%c"
#define PRINTF_BYTE_TO_BINARY_INT8(i)    \
    (((i) & 0x80ll) ? '1' : '0'), \
    (((i) & 0x40ll) ? '1' : '0'), \
    (((i) & 0x20ll) ? '1' : '0'), \
    (((i) & 0x10ll) ? '1' : '0'), \
    (((i) & 0x08ll) ? '1' : '0'), \
    (((i) & 0x04ll) ? '1' : '0'), \
    (((i) & 0x02ll) ? '1' : '0'), \
    (((i) & 0x01ll) ? '1' : '0')

#define PRINTF_BINARY_PATTERN_INT16 \
    PRINTF_BINARY_PATTERN_INT8              PRINTF_BINARY_PATTERN_INT8
#define PRINTF_BYTE_TO_BINARY_INT16(i) \
    PRINTF_BYTE_TO_BINARY_INT8((i) >> 8),   PRINTF_BYTE_TO_BINARY_INT8(i)
#define PRINTF_BINARY_PATTERN_INT32 \
    PRINTF_BINARY_PATTERN_INT16             PRINTF_BINARY_PATTERN_INT16
#define PRINTF_BYTE_TO_BINARY_INT32(i) \
    PRINTF_BYTE_TO_BINARY_INT16((i) >> 16), PRINTF_BYTE_TO_BINARY_INT16(i)
#define PRINTF_BINARY_PATTERN_INT64    \
    PRINTF_BINARY_PATTERN_INT32             PRINTF_BINARY_PATTERN_INT32
#define PRINTF_BYTE_TO_BINARY_INT64(i) \
    PRINTF_BYTE_TO_BINARY_INT32((i) >> 32), PRINTF_BYTE_TO_BINARY_INT32(i)

/*R/W to memory*/

void writew(uint32_t val, volatile uint32_t *addr)
{
    asm volatile("sw %0, 0(%1)" : : "r"(val), "r"(addr));
}


uint32_t irq_served = 0;

#define FAST_IRQ_GENERIC(id)                                                        \
do {                                                                                \
    irq_id = id;                                                                    \
    if (irq_mode == IRQ_MODE_RND)                                                   \
    {                                                                               \
        asm volatile("csrr %0, 0x344": "=r" (irq_pending32_std));                   \
    }                                                                               \
    irq_pending32_std &= (~(1 << irq_id));                                          \
    writew(irq_pending32_std, RND_STALL_REG_14);                                    \
    if (irq_mode == IRQ_MODE_RND)                                                   \
    {                                                                               \
        irq_served++;                                                               \
        irq_mode = IRQ_MODE_STD;                                                    \
        writew(irq_mode, RND_STALL_REG_10);                                         \
        irq_mode = IRQ_MODE_RND;                                                    \
        writew(irq_mode, RND_STALL_REG_10);                                         \
    }                                                                               \
    else                                                                            \
    {                                                                               \
        asm volatile("csrr %0, mstatus": "=r" (mmstatus));                          \
        mmstatus &= (~(1 << 7));                                                    \
        asm volatile("csrw mstatus, %[mmstatus]" : : [mmstatus] "r" (mmstatus));    \
    }                                                                               \
} while(0)

void software_irq_handler(void)
{
    FAST_IRQ_GENERIC(SOFTWARE_IRQ_ID);
}

void timer_irq_handler(void) //TODO: do this here
{
    FAST_IRQ_GENERIC(TIMER_IRQ_ID);
}

void external_irq_handler(void)
{
    FAST_IRQ_GENERIC(EXTERNAL_IRQ_ID);
}

void fast0_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST0_IRQ_ID);
}

void fast1_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST1_IRQ_ID);
}

void fast2_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST2_IRQ_ID);
}

void fast3_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST3_IRQ_ID);
}

void fast4_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST4_IRQ_ID);
}

void fast5_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST5_IRQ_ID);
}

void fast6_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST6_IRQ_ID);
}

void fast7_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST7_IRQ_ID);
}

void fast8_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST8_IRQ_ID);
}

void fast9_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST9_IRQ_ID);
}

void fast10_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST10_IRQ_ID);
}

void fast11_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST11_IRQ_ID);
}

void fast12_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST12_IRQ_ID);
}

void fast13_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST13_IRQ_ID);
}

void fast14_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST14_IRQ_ID);
}

void fast15_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST15_IRQ_ID);
}

uint32_t random_num(uint32_t upper_bound, uint32_t lower_bound)
{

    uint32_t random_num = *((int *)0x15001000);
    uint32_t num = (random_num  % (upper_bound - lower_bound + 1)) + lower_bound;
    return num;
}
void mstatus_enable(uint32_t bit_enabled)
{
    asm volatile("csrr %0, mstatus": "=r" (mmstatus));
    mmstatus |= (1 << bit_enabled);
    asm volatile("csrw mstatus, %[mmstatus]" : : [mmstatus] "r" (mmstatus));
}

void mstatus_disable(uint32_t bit_disabled)
{
    asm volatile("csrr %0, mstatus": "=r" (mmstatus));
    mmstatus &= (~(1 << bit_disabled));
    asm volatile("csrw mstatus, %[mmstatus]" : : [mmstatus] "r" (mmstatus));
}

// integer matrix multiplication
void mat_mult(uint32_t mat1[MAT_DIM][MAT_DIM], uint32_t mat2[MAT_DIM][MAT_DIM], uint32_t res[MAT_DIM][MAT_DIM])
{
    uint32_t i, j, k;
    for (i = 0; i < MAT_DIM; i++)
    {
        for (j = 0; j < MAT_DIM; j++)
        {
            res[i][j] = 0;
            for (k = 0; k < MAT_DIM; k++)
                res[i][j] += mat1[i][k] * mat2[k][j];
        }
    }
}

int main(int argc, char *argv[])
{

#ifdef RANDOM_MEM_STALL
    printf("ACTIVATING RANDOM D/I MEMORY STALLS: ");
    activate_random_stall();
    printf("OK\n");
#endif

    printf("TEST 1 - TRIGGER ALL IRQS IN SEQUENCE: ");

    // Enable all mie (need to store)
    ie_mask32_std = 0xFFFFFFFF;

    asm volatile("csrw 0x304, %[ie_mask32_std]"
                  : : [ie_mask32_std] "r" (ie_mask32_std));

    // software defined irq gen mode
    writew(IRQ_MODE_SD, RND_STALL_REG_10);

    // disable mstatues.mie
    mstatus_disable(MSTATUS_MIE_BIT);

    printf("OK\n");

    // TODO: needs to make sure preivous test finished

    //-------------------------------------------------------------------------------------------------------------------------------------------
    //-------------------------------------------------------------------------------------------------------------------------------------------

    //////////////////////
    // All IRQS AT ONCE //
    //////////////////////

    // Test 2 is a test where the core is stressed:
    // words are generated:
    // - all irqs are triggered at the same time
    // - all irqs are enabled
    // We expect the core to serve them one after the oteher
    // in the correct priority order

    printf("TEST 2 - TRIGGER ALL IRQS AT ONCE: ");

    // Enable all mie (need to store)
    ie_mask32_std = 0xFFFFFFFF;

    asm volatile("csrw 0x304, %[ie_mask32_std]"
                  : : [ie_mask32_std] "r" (ie_mask32_std));

    // Multiple interrupts at a time
    irq_pending32_std = 0xFFFFFFFF;

    // disable mstatues.mie
    mstatus_disable(MSTATUS_MIE_BIT);

    // for this test we only write once
    writew(irq_pending32_std, RND_STALL_REG_14);

    for (int i = 0; i < IRQ_NUM; i++)
    {
        // sample irq_pending
        prev_irq_pending32_std = irq_pending32_std;

        // enable mstatus.mie
        mstatus_enable(MSTATUS_MIE_BIT);

        // wait for nex irq to be served
        while(prev_irq_pending32_std == irq_pending32_std);

        // irq_id sampling and testing
        if(IRQ_ID_PRIORITY[i] != irq_id)
        {
            printf("\nERR: IRQ served in wrong order %d %d\n", IRQ_ID_PRIORITY[i], irq_id);
            return ERR_CODE_TEST_2;
        }
    }
    printf("OK\n");

    //-------------------------------------------------------------------------------------------------------------------------------------------
    //-------------------------------------------------------------------------------------------------------------------------------------------

    printf("TEST 3 - RANDOMIZE: "); //TODO: improve messages

    ///////////////////////////////
    // Random test with masking  //
    ///////////////////////////////

    // Test 3 is a random test where two 32 bit-wide
    // words are generated:
    // - a mask (rnd_ie_mask)
    // - and a value for the irq_pending
    //
    //

    irq_processed     = 1;
    irq_id            = 0;
    ie_mask32_std = 0;
    irq_pending32_std = 0;

    // build ie word randomly
    for (int i = 0; i < RND_IE_NUM; ++i)
    {
        // todo here we can set to 1 irqs already set
        bit_to_set = random_num(31, 0);
        ie_mask32_std |= (1 << bit_to_set);
    }

    // mask to consider only implemented irqs
    ie_mask32_std = ie_mask32_std & STD_IRQ_MASK;

    // write the mask to mie
    asm volatile("csrw 0x304, %[ie_mask32_std]" : : [ie_mask32_std] "r" (ie_mask32_std));


    // build irq word randomly
    for (int i = 0; i < RND_IRQ_NUM; ++i)
    {
        // todo here we can set to 1 also non-implemented irqs + irqs already set
        bit_to_set = random_num(31, 0);
        irq_pending32_std |= (1 << bit_to_set);
    }

    // mask to consider only implemented irqs
    irq_pending32_std = irq_pending32_std & STD_IRQ_MASK;

    first_irq_pending32_std = irq_pending32_std;

    uint32_t irq_to_serve_num = 0;
    uint32_t irq_served_num = 0;

    // build words to be tested
    for (int i = 0; i < 32; ++i)
    {
        if ((1 << i) & first_irq_pending32_std & ie_mask32_std)
        {
            irq_to_test32_std |= (1 << i);
        }
    }

    // disable mstatues.mie
    mstatus_disable(MSTATUS_MIE_BIT);

    // for this test we only write once
    writew(irq_pending32_std, RND_STALL_REG_14);

    for (int i = 0; i < IRQ_NUM; ++i)
    {
        if (IRQ_ID_PRIORITY[i] <= 31 && (1 << IRQ_ID_PRIORITY[i] & irq_to_test32_std))
        {
            // sample irq_pending
            prev_irq_pending32_std = irq_pending32_std;

            // enable mstatus.mie
            mstatus_enable(MSTATUS_MIE_BIT);

            // wait for next irq to be served
            while(prev_irq_pending32_std == irq_pending32_std);
            //{ printf("waiting for irq %u \n", IRQ_ID_PRIORITY[i]);}

            // irq_id sampling and testing
            if(IRQ_ID_PRIORITY[i] != irq_id)
            {
                printf("\nERR: IRQ served in wrong order %d %d\n", IRQ_ID_PRIORITY[i], irq_id);
                return ERR_CODE_TEST_3;
            }
        }
    }

    if(irq_pending32_std != ((~ie_mask32_std) & first_irq_pending32_std))
    {
        printf("\nERR: wrong number of irq served\n"
            "first_irq_pending32_std: "PRINTF_BINARY_PATTERN_INT32"\n"
            "ie_mask32_std:           "PRINTF_BINARY_PATTERN_INT32"\n"
            "irq_to_test32_std:       "PRINTF_BINARY_PATTERN_INT32"\n"
            "irq_pending32_std:       "PRINTF_BINARY_PATTERN_INT32"\n",
            PRINTF_BYTE_TO_BINARY_INT32(first_irq_pending32_std),
            PRINTF_BYTE_TO_BINARY_INT32(ie_mask32_std),
            PRINTF_BYTE_TO_BINARY_INT32(irq_to_test32_std),
            PRINTF_BYTE_TO_BINARY_INT32(irq_pending32_std));
        return ERR_CODE_TEST_3;
    }

    printf("OK\n");

    // ///////////////////////////////
    // // TEST 4: PC Trig Test      //
    // ///////////////////////////////

    // // Test 4: a software interrupt (id = 3) is raised
    // // as the program counter assumes a desired value


    // printf("\nTEST 4: PC TRIG\n");

    // // Enable all mie (need to store)
    // regVal = 0xFFFFFFFF;
    // asm volatile("csrw 0x304, %[regVal]"
    //               : : [regVal] "r" (regVal));

    // // set desired PC value
    // writew(0x0000043e, RND_STALL_REG_13);
    // // switch to PC_TRIG mode
    // writew(IRQ_MODE_PC_TRIG, RND_STALL_REG_10);

    // mstatus_enable(MSTATUS_MIE_BIT);

    // mat_mult(mat1, mat2, res);

    // printf("\nResult matrix is\n");
    // for (int i = 0; i < MAT_DIM; i++)
    // {
    //     // mstatus_enable(MSTATUS_MIE_BIT);
    //     for (int j = 0; j < MAT_DIM; j++)
    //     {
    //         print_dec(res[i][j]);
    //         mstatus_enable(MSTATUS_MIE_BIT);
    //         print_chr(' ');
    //     }
    //     printf("\n");
    // }

    /////////////////////////////////
    // TEST 5: Random IRQs bombing //
    /////////////////////////////////

    // Test 5: random irqs arrive randomly
    // while the core is executing some task (e.g. matrix mult)

    printf("\nTEST 5 - RANDOM IRQS BOMBING: \n");

    mstatus_disable(MSTATUS_MIE_BIT);

    // Enable all mie and miex bits
    ie_mask32_std = 0xFFFFFFFF;

    asm volatile("csrw 0x304, %[ie_mask32_std]" : : [ie_mask32_std] "r" (ie_mask32_std));

    writew(RND_IRQ_MIN_CYCLES, RND_STALL_REG_11);
    writew(RND_IRQ_MAX_CYCLES, RND_STALL_REG_12);

    // random irq gen mode:
    // the random interrupt generator will
    // keep on generating random interrupt vectors
    irq_mode = IRQ_MODE_RND;
    writew(irq_mode, RND_STALL_REG_10);

    irq_served = 0;

    mstatus_enable(MSTATUS_MIE_BIT);

    mat_mult(mat1, mat2, res);

    // disable irqs and check the result
    mstatus_disable(MSTATUS_MIE_BIT);

    printf("%d IRQ SERVED\n", irq_served);

     irq_served = 0;


    for (int i = 0; i < MAT_DIM; i++)
    {
        // mstatus_enable(MSTATUS_MIE_BIT);
        for (int j = 0; j < MAT_DIM; j++)
        {
            if(res[i][j] != res_expected[i][j])
            {
                printf("\nERR: wrong\nExpected %d Got %d at address %x\n", res_expected[i][j], res[i][j], &res[i][j]);
                return ERR_CODE_TEST_5;
            }
        }
    }

    return EXIT_SUCCESS;
}





