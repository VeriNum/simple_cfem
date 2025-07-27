#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "vecmat.h"
#include "bandmat.h"

//ldoc on
/**
 * ### Implementation
 * 
 */
// Allocate a band matrix
double* malloc_bandmat(int n, int b)
{
    return malloc_vecmat(n, b+1);
}

// Convert dense n-by-n A to band matrix P with bandwidth bw
double* dense_to_band(double* A, int n, int bw)
{
    double* P = malloc_bandmat(n, bw);
    for (int d = 0; d <= bw; ++d)
        for (int j = d; j < n; ++j) {
            int i = j-d;
            P[j+d*n] = A[i+j*n];
        }
    return P;
}

/**
 * #### Printing a band matrix
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
void bandmat_print(double* PA)
{
    vecmat_head_t* head = vecmat(PA);
    int n = head->m, bw = head->n-1;

    for (int i = 0; i < n; ++i) {
        for (int d = 0; d <= bw && d <= i; ++d)
            printf("  % 6.3g", PA[i+d*n]);
        printf("\n");
    }
}

/**
 * #### Band Cholesky and triangular solves
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
// Factor a band matrix
void bandmat_factor(double* PA)
{
    vecmat_head_t* head = vecmat(PA);
    int n = head->m, bw=head->n-1;
    
    for (int k = 0; k < n; ++k) {

        // Compute kth diagonal element
        assert(PA[k] >= 0);
        PA[k] = sqrt(PA[k]);

        // Scale across the row
        for (int j = k+1; j < n && j <= k+bw; ++j)
            PA[j+n*(j-k)] /= PA[k];

        // Apply the Schur complement update
        for (int j = k+1; j < n && j <= k+bw; ++j)
            for (int i = k+1; i <= j; ++i)
                PA[j+n*(j-i)] -= PA[i+n*(i-k)]*PA[j+n*(j-k)];
    }    
}

// Solve a linear system with a band Cholesky factorization
void bandmat_solve(double* PR, double* x)
{
    vecmat_head_t* head = vecmat(PR);
    int n = head->m, bw = head->n-1;
    
    // Forward substitution
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int dj = 1; dj <= bw && dj <= i; ++dj)
            bi -= PR[i+dj*n]*x[i-dj];
        x[i] = bi/PR[i];
    }

    // Backward substitution
    for (int i = n-1; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j <= i+bw && j < n; ++j)
            yi -= PR[j+(j-i)*n]*x[j];
        x[i] = yi/PR[i];
    }
}

