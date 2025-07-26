#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "vecmat.h"
#include "bandmat.h"

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

// Factor a band matrix
void bandmat_factor(double* PA)
{
    vecmat_head_t* head = vecmat(PA);
    int n = head->m, bw=head->n-1;
    
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
