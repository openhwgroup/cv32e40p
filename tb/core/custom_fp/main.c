#include <stdio.h>
#include <stdlib.h>

void matmulNxN(float* matA, float* matB, float* matC, int N);

#define N 5

float matA[N*N], matB[N*N];
float matC[N*N], matC_ref[N*N];

int main(int argc, char *argv[])
{

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
