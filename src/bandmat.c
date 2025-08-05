#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "vecmat.h"
#include "bandmat.h"

//ldoc on
/**
 * ## Band matrix construction
 * 
 */
// Allocate a band matrix
vecmat_t* malloc_bandmat(int n, int b)
{
  vecmat_t *vm = malloc_vecmat(n*(b+1));
  vm->m=n; vm->n=b+1;
  return vm;
}

// Convert dense n-by-n A to band matrix P with bandwidth bw
vecmat_t* dense_to_band(vecmat_t* A, int bw)
{
    int n = A->n;
    vecmat_t* P = malloc_bandmat(n, bw);
    for (int d = 0; d <= bw; ++d)
        for (int j = d; j < n; ++j) {
            int i = j-d;
            P->data[j+d*n] = A->data[i+j*n];
        }
    return P;
}

/**
 * ## Printing a band matrix
 * 
 * When printing a band matrix, we usually print just the structural
 * nonzeros.  Unless the matrix is very small, trying to introduce
 * spaces or dots for structural zeros usually just makes the output
 * too big to fit on a screen; hence, we will *almost* just print the
 * underlying `n`-by-`b+1` data array.  The only difference is that we
 * will not bother to print out the "don't care" values that are at
 * the start of the superdiagonal representations (since they will be
 * garbage unless we zeroed them out, and anyway -- we don't care
 * about them).
 * 
 */
// Print band format array
void bandmat_print(vecmat_t* PA)
{
    int n = PA->m, bw = PA->n-1;

    for (int i = 0; i < n; ++i) {
        for (int d = 0; d <= bw && d <= i; ++d)
            printf("  % 6.3g", PA->data[i+d*n]);
        printf("\n");
    }
}

/**
 * ## Band Cholesky and triangular solves
 * 
 * When computing a Cholesky factorization of a band matrix, the Schur
 * complement update step only affects elements that were already
 * structural nonzeros.  Hence, Cholesky factorization of a band
 * matrix can be done purely within the band data structure.  The
 * algorithm is essentially identical to the ordinary Cholesky
 * factorization, except with indexing appropriate to the packed data
 * structure.  As with the dense Cholesky implementation in
 * `vecmat_t`, we only ever reference the upper triangle of the
 * matrix, and we overwrite the input arrays (representing the upper
 * triangle of a symmetric input) by the output (representing an upper
 * triangular Cholesky factor).  Also as with dense Cholesky, we will
 * error out if we encounter a negative diagonal in a Schur complement
 * (violating the assumption of positive definiteness).
 * 
 */
void bandmat_factor(vecmat_t* PA)
{
    int n = PA->m, bw=PA->n-1;
    
    for (int k = 0; k < n; ++k) {

        // Compute kth diagonal element
        assert(PA->data[k] >= 0);
        PA->data[k] = sqrt(PA->data[k]);

        // Scale across the row
        for (int j = k+1; j < n && j <= k+bw; ++j)
            PA->data[j+n*(j-k)] /= PA->data[k];

        // Apply the Schur complement update
        for (int j = k+1; j < n && j <= k+bw; ++j)
            for (int i = k+1; i <= j; ++i)
                PA->data[j+n*(j-i)] -= PA->data[i+n*(i-k)]*PA->data[j+n*(j-k)];
    }    
}

/**
 * The `bandmat_solve(PR, x)` routine uses a band Cholesky factor $R$
 * of the matrix $A$ to solve $Ax = b$.  The `PR` input argument gives
 * the Cholesky factor (as computed by `bandmat_cholesky`);
 * on input the `x` argument should be set to the system right-hand side,
 * and on output it will be the solution vector.
 */
void bandmat_solve(vecmat_t* PR, double* x)
{
    int n = PR->m, bw = PR->n-1;
    
    // Forward substitution
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int dj = 1; dj <= bw && dj <= i; ++dj)
            bi -= PR->data[i+dj*n]*x[i-dj];
        x[i] = bi/PR->data[i];
    }

    // Backward substitution
    for (int i = n-1; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j <= i+bw && j < n; ++j)
            yi -= PR->data[j+(j-i)*n]*x[j];
        x[i] = yi/PR->data[i];
    }
}

