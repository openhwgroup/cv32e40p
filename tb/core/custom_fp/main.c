#include <stdio.h>
#include <stdlib.h>

void matmulNxN(float* matA, float* matB, float* matC, int N);

#define N 5

int main(int argc, char *argv[])
{

  float matA[N*N], matB[N*N];
  float matC[N*N];
  float tmpA, tmpB, tmpC;
  unsigned int ui;

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

  printf("matA = \n");
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      memcpy(&ui, &matA[i*N+j], sizeof(ui));
      printf("%x ", ui);
    }
    printf("\n");
  }

  printf("matB = \n");
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      memcpy(&ui, &matB[i*N+j], sizeof(ui));
      printf("%x ", ui);
    }
    printf("\n");
  }

  matmulNxN(matA, matB, matC, N);

  printf("matC = matA * matB = \n");
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      memcpy(&ui, &matC[i*N+j], sizeof(ui));
      printf("%x ", ui);
    }
    printf("\n");
  }
  return EXIT_SUCCESS;
}