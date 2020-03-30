#include <stdio.h>
#include <stdlib.h>

void activate_random_stall(void)
{
  // Address vector for rnd_stall_reg, to control memory stalls/interrupt
  volatile unsigned int *rnd_stall_reg[16];

  // Setup the address vector
  rnd_stall_reg[0] = 0x16000000;
  for (int i = 1; i < 16; i++) {
    rnd_stall_reg[i] = rnd_stall_reg[i-1] + 1; // It is a pointer to int ("+ 1" means "the next int")
  }

  // INSTRUCTION MEMORY
  // Set stall mode (standard=1, random=2) (rnd_stall_reg[2])
  *rnd_stall_reg[2] = 0x02;
  // Set max n. stalls on both GNT and VALID for RANDOM mode (rnd_stall_reg[4])
  *rnd_stall_reg[4] = 0x0a;
  // Set n. stalls on  GNT (rnd_stall_reg[6])
  *rnd_stall_reg[6] = 0x00;
  // Set n. stalls on VALID (rnd_stall_reg[8])
  *rnd_stall_reg[8] = 0x00;

  // DATA MEMORY
  // Set stall mode (standard=1, random=2) (rnd_stall_reg[3])
  *rnd_stall_reg[3] = 0x02;
  // Set max n. stalls on both GNT and VALID for RANDOM mode (rnd_stall_reg[5])
  *rnd_stall_reg[5] = 0x0a;
  // Set n. stalls on  GNT (rnd_stall_reg[7])
  *rnd_stall_reg[7] = 0x00;
  // Set n. stalls on VALID (rnd_stall_reg[9])
  *rnd_stall_reg[9] = 0x00;

  /* Activating stalls on D and I Mem has to be done as last operation. Do not change the order. */
  // Enable/disable stalls on D-MEM (rnd_stall_reg[1])
  *rnd_stall_reg[1] = 0x01;
  // Enable/disable stalls on I-MEM (rnd_stall_reg[0])
  *rnd_stall_reg[0] = 0x01;
}

int main(int argc, char *argv[])
{
#ifdef RANDOM_MEM_STALL
    activate_random_stall();
#endif
    /* inline assembly */
    asm volatile("ecall");
    /* write something to stdout */
    printf("hello world!\n");
    return EXIT_SUCCESS;
}
