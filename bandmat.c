#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bandmat.h"

// Allocate a band matrix
bandmat_t* malloc_bandmat(int n, int b)
{
    bandmat_t* bandmat = (bandmat_t*) malloc(sizeof(bandmat_t));
    bandmat->P = malloc(n * (b+1) * sizeof(double));
    bandmat->n = n;
    bandmat->b = b;
    return bandmat;
}

// Convert dense n-by-n A to band matrix P with bandwidth bw
bandmat_t* dense_to_band(double* A, int n, int bw)
{
    bandmat_t* B = malloc_bandmat(n, bw);
    double* P = B->P;
    for (int d = 0; d <= bw; ++d)
        for (int j = d; j < n; ++j) {
            int i = j-d;
            P[j+d*n] = A[i+j*n];
        }
    return B;
}

// Free a band matrix
void free_bandmat(bandmat_t* bandmat)
{
    free(bandmat->P);
    free(bandmat);
}

// Clear the contents of a band matrix
void bandmat_clear(bandmat_t* bandmat)
{
    double* P = bandmat->P;
    int n = bandmat->n;
    int b = bandmat->b;
    memset(P, 0, n * (b+1) * sizeof(double));
}

// Factor a band matrix
void bandmat_factor(bandmat_t* bandmat)
{
    double* PA = bandmat->P;
    int n = bandmat->n;
    int bw = bandmat->b;
    
    for (int k = 0; k < n; ++k) {

        // Compute kth diagonal element
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
void bandmat_solve(bandmat_t* bandmat, double* x)
{
    double* PR = bandmat->P;
    int n = bandmat->n;
    int bw = bandmat->b;
    
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

// Print band format array
void print_bandmat(bandmat_t* bandmat)
{
    double* PA = bandmat->P;
    int n = bandmat->n;
    int bw = bandmat->b;

    for (int i = 0; i < n; ++i) {
        for (int d = 0; d <= bw && d <= i; ++d)
            printf("  % 6.3g", PA[i+d*n]);
        printf("\n");
    }    
}
