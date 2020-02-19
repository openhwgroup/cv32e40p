// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

#ifndef FIRMWARE_H
#define FIRMWARE_H

#include <stdint.h>
#include <stdbool.h>

// irq.c
uint32_t *irq(uint32_t *regs, uint32_t irqs);
void timer_irq_handler(void);
// print.c
void print_chr(char ch);
void print_str(const char *p);
void print_dec(unsigned int val);
void print_hex(unsigned int val, int digits);

// sieve.c
void sieve(void);

// multest.c
uint32_t hard_mul(uint32_t a, uint32_t b);
uint32_t hard_mulh(uint32_t a, uint32_t b);
uint32_t hard_mulhsu(uint32_t a, uint32_t b);
uint32_t hard_mulhu(uint32_t a, uint32_t b);
void multest(void);

// stats.c
void stats(void);

//R/W
static inline  void writew(uint32_t val, volatile uint32_t *addr);	

void software_irq_handler(void) __attribute__ ((interrupt ("machine")));
void timer_irq_handler(void)    __attribute__ ((interrupt ("machine")));
void external_irq_handler(void) __attribute__ ((interrupt ("machine")));

void fast0_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fast1_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fast2_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fast3_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fast4_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fast5_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fast6_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fast7_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fast8_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fast9_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fast10_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fast11_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fast12_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fast13_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fast14_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fast14_irq_handler(void) __attribute__ ((interrupt ("machine")));

void nmi_irq_handler(void)    __attribute__ ((interrupt ("machine")));

void fastx0_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fastx1_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fastx2_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fastx3_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fastx4_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fastx5_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fastx6_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fastx7_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fastx8_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fastx9_irq_handler(void)  __attribute__ ((interrupt ("machine")));
void fastx10_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx11_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx12_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx13_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx14_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx15_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx16_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx17_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx18_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx19_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx20_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx21_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx22_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx23_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx24_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx25_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx26_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx27_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx28_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx29_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx30_irq_handler(void) __attribute__ ((interrupt ("machine")));
void fastx31_irq_handler(void) __attribute__ ((interrupt ("machine")));
#endif
