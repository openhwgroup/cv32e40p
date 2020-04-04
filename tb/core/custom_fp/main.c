#include <stdio.h>
#include <stdlib.h>

void matmulNxN(float* matA, float* matB, float* matC, int N);

#define N 5

float matA[N*N], matB[N*N];
float matC[N*N], matC_ref[N*N];

void activate_random_stall(void)
{
  // Address vector for rnd_stall_reg, to control memory stalls/interrupt
  volatile unsigned int *rnd_stall_reg[16];

  // Setup the address vector
  rnd_stall_reg[0] = 0x16000000;
  for (int i = 1; i < 16; i++) {
    rnd_stall_reg[i] = rnd_stall_reg[i-1] + 1; // It is a pointer to int ("+ 1" means "the next int")
  }

  /* The interposition of the stall generator between CPU and MEM should happen BEFORE the stall generetor is active */
  // Interpose the stall generator between CPU and D-MEM (rnd_stall_reg[1])
  *rnd_stall_reg[1] = 0x01;
  // Interpose the stall generator between CPU and I-MEM (rnd_stall_reg[0])
  *rnd_stall_reg[0] = 0x01;

  // DATA MEMORY
  // Set max n. stalls on both GNT and VALID for RANDOM mode (rnd_stall_reg[5])
  *rnd_stall_reg[5] = 0x05;
  // Set n. stalls on  GNT (rnd_stall_reg[7])
  *rnd_stall_reg[7] = 0x05;
  // Set n. stalls on VALID (rnd_stall_reg[9])
  *rnd_stall_reg[9] = 0x05;

  // INSTRUCTION MEMORY
  // Set max n. stalls on both GNT and VALID for RANDOM mode (rnd_stall_reg[4])
  *rnd_stall_reg[4] = 0x05;
  // Set n. stalls on  GNT (rnd_stall_reg[6])
  *rnd_stall_reg[6] = 0x05;
  // Set n. stalls on VALID (rnd_stall_reg[8])
  *rnd_stall_reg[8] = 0x05;

  /* Activating stalls on D and I Mem has to be done as last operation. Do not change the order. */
  // Set stall mode on D-MEM (off=0, standard=1, random=2) (rnd_stall_reg[3])
  *rnd_stall_reg[3] = 0x02;
  // Set stall mode on I-MEM (off=0, standard=1, random=2) (rnd_stall_reg[2])
  *rnd_stall_reg[2] = 0x02;
}

int main(int argc, char *argv[])
{

#ifdef RANDOM_MEM_STALL
    activate_random_stall();
#endif
  float tmpA, tmpB, tmpC;
  int error = 0;

  asm volatile("ecall");

  tmpA = 1.14f;
  tmpB = 0.75f;
  tmpC = 12.1f;

  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      matA[i*N+j] = tmpA;
      matB[i*N+j] = tmpB;
    }
    tmpA = tmpA - tmpC;
    tmpB = tmpB + tmpC;
  }

  for (int i = 0; i < N; ++i) {
    matC_ref[i] = 142.2150115966796875f;
  }
  for (int i = N; i < 2*N; ++i) {
    matC_ref[i] = -1367.260009765625f;
  }
  for (int i = 2*N; i < 3*N; ++i) {
    matC_ref[i] = -2876.7353515625f;
  }
  for (int i = 3*N; i < 4*N; ++i) {
    matC_ref[i] = -4386.2109375f;
  }
  for (int i = 4*N; i < 5*N; ++i) {
    matC_ref[i] = -5895.685546875f;
  }

  matmulNxN(matA, matB, matC, N);

  for (int i = 0; i < N*N; ++i) {
    if (matC_ref[i] != matC[i]) {
      error++;
      printf("Error at index %d, expected %x, got %x\n", i, (*(int*)&matC_ref[i]), (*(int*)&matC[i]));
    }
  }

  if (error)
    return error;
  else
    return EXIT_SUCCESS;
}
