#ifndef BANDMAT_H
#define BANDMAT_H

/*
typedef struct bandmat_t {
    double* P;  // Storage pointer
    int n;      // Dimension of matrix
    int b;      // Bandwidth
} bandmat_t;
*/

typedef double bandmat_t;

// Allocate a new bandmat (and maybe populate from a dense matrix)
bandmat_t* malloc_bandmat(int n, int b);
bandmat_t* dense_to_band(double* A, int n, int bw);

// Cholesky and linear solve with Cholesky
void bandmat_factor(bandmat_t* bandmat);
void bandmat_solve(bandmat_t* bandmat, double* x);

// Print a bandmat
void bandmat_print(bandmat_t* bandmat);

#endif /* BANDMAT_H */
