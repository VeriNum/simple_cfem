#ifndef BANDMAT_H
#define BANDMAT_H

// Allocate a new bandmat (and maybe populate from a dense matrix)
double* malloc_bandmat(int n, int b);
double* dense_to_band(double* A, int n, int bw);

// Cholesky and linear solve with Cholesky
void bandmat_factor(double* PA);
void bandmat_solve(double* PR, double* x);

// Print a bandmat
void bandmat_print(double* PA);

#endif /* BANDMAT_H */
