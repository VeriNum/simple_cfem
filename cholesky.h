#ifndef CHOLESKY_H
#define CHOLESKY_H

// Compute Cholesky of SPD matrix in band storage
void band_cholesky(double* PA, int n, int b);

// Solve linear system with Cholesky in band storage
void bcholesky_solve(double* PR, double* x, int n, int b);

#endif /* CHOLESKY_H */
