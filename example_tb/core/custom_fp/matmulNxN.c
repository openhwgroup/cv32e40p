void matmulNxN(float* matA, float* matB , float* matC, int N)
{
  float tot;
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      tot = 0;
      for (int k = 0; k < N; ++k) {
        tot = tot + matA[i*N+k] * matB[k*N+j];
      }
      matC[i*N+j] = tot;
    }
  }
}
