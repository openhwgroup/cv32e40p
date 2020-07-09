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

void software_irq_handler(void) __attribute__ ((interrupt));
void timer_irq_handler(void)    __attribute__ ((interrupt));
void external_irq_handler(void) __attribute__ ((interrupt));

void fast0_irq_handler(void)  __attribute__ ((interrupt));
void fast1_irq_handler(void)  __attribute__ ((interrupt));
void fast2_irq_handler(void)  __attribute__ ((interrupt));
void fast3_irq_handler(void)  __attribute__ ((interrupt));
void fast4_irq_handler(void)  __attribute__ ((interrupt));
void fast5_irq_handler(void)  __attribute__ ((interrupt));
void fast6_irq_handler(void)  __attribute__ ((interrupt));
void fast7_irq_handler(void)  __attribute__ ((interrupt));
void fast8_irq_handler(void)  __attribute__ ((interrupt));
void fast9_irq_handler(void)  __attribute__ ((interrupt));
void fast10_irq_handler(void) __attribute__ ((interrupt));
void fast11_irq_handler(void) __attribute__ ((interrupt));
void fast12_irq_handler(void) __attribute__ ((interrupt));
void fast13_irq_handler(void) __attribute__ ((interrupt));
void fast14_irq_handler(void) __attribute__ ((interrupt));
void fast14_irq_handler(void) __attribute__ ((interrupt));
void fast15_irq_handler(void) __attribute__ ((interrupt));
#endif
