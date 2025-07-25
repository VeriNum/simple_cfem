//ldoc on
/**
---
title: Band Cholesky in C
author: David Bindel
date: 2025-07-24
---

## Testing setup

We start with an spd system $Ax = b$ where $A$ is a 6-by-6 pentadiagonal
matrix.  The matrix $A$ and the right hand side vector $b$ generated
randomly in Julia, and a reference solution was also computed in Julia.
We access these with functions `get_Aref`, `get_bref`, and `get_xref`
that copy the reference values into an output argument.
 */
//ldoc off

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

void get_Aref(double* A)
{
    static double Aref[] = {
        // Randomly generated matrix (6-by-6)...
        5.611573028354077,
        0.4567405138512043,
        1.5563566615211313,
        0.0,
        0.0,
        0.0,
        0.4567405138512043,
        4.757747564652157,
        1.395776410174324,
        0.31352657528440375,
        0.0,
        0.0,
        1.5563566615211313,
        1.395776410174324,
        5.689183174271518,
        1.0184064385847038,
        1.0560604548088794,
        0.0,
        0.0,
        0.31352657528440375,
        1.0184064385847038,
        5.703049575775514,
        1.509589258389374,
        1.83183662372477,
        0.0,
        0.0,
        1.0560604548088794,
        1.509589258389374,
        5.7857136854295845,
        0.8755526167936731,
        0.0,
        0.0,
        0.0,
        1.83183662372477,
        0.8755526167936731,
        4.25791871147544
    };
    memcpy(A, Aref, 36*sizeof(double));
}

void get_bref(double* b)
{
    static double bref[] = {
        // Randomly generated vector (len 6)...
        0.9176326489491068,
        0.8622794808080309,
        0.59767235440732,
        0.5456893881835098,
        0.4788475407133893,
        0.597614144120541
    };
    memcpy(b, bref, 6*sizeof(double));
}

void get_xref(double* x)
{
    static double xref[] = {
        // Reference solution vector for Ax = b (len 6)...
        0.1479665631498538,
        0.1623141664502468,
        0.008463367436900621,
        0.03391852175929072,
        0.055050669463981176,
        0.11444116927844857
    };
    memcpy(x, xref, 6*sizeof(double));
}

//ldoc on
/**
The `check_solution` function returns the norm of the residual
$r = b-Ax$ for a proposed solution.  We have a healthy sense of paranoia,
so we will check to make sure that our tester produces a small residual
with the reference solution.
*/

double check_solution(double* x)
{
    double A[36], b[6];

    get_Aref(A);
    get_bref(b);
    for (int j = 0; j < 6; ++j)
        for (int i = 0; i < 6; ++i)
            b[i] -= A[i+6*j]*x[j];

    double rnorm = 0.0;
    for (int j = 0; j < 6; ++j)
        rnorm += b[j]*b[j];

    return sqrt(rnorm);
}

void test_check_solution()
{
    double x[6];
    get_xref(x);
    printf("Check that reference solution is good / tester works: ");
    printf("%g\n", check_solution(x));
}


/**
## Dense Cholesky

Our first step is to develop a *dense* Cholesky solver.  We use a
standard column-major dense storage format, but we only ever bother
to reference the upper triangle.
*/

// Compute Cholesky of and n-by-n matrix A, overwriting storage.
void dense_cholesky(double* A, int n)
{
    for (int k = 0; k < n; ++k) {

        // Compute kth diagonal element R(k,k)
        A[k+n*k] = sqrt(A[k+n*k]);

        // Scale across the row R(k,j) = A(k,j)/R(k,k)
        for (int j = k+1; j < n; ++j)
            A[k+n*j] /= A[k+n*k];

        // Apply the Schur complement update S(i,j) -= R(k,i)*R(k,j)
        for (int j = k+1; j < n; ++j)
            for (int i = k+1; i <= j; ++i)
                A[i+n*j] -= A[k+n*i]*A[k+n*j];
    }
}

// Overwrite input variable x with R \ (R^T \ x)
void cholesky_solve(double* R, double* x, int n)
{
    // Forward substitution
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int j = 0; j < i; ++j)
            bi -= R[j+i*n]*x[j];
        x[i] = bi/R[i+i*n];
    }

    // Backward substitution
    for (int i = n-1; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j < n; ++j)
            yi -= R[i+j*n]*x[j];
        x[i] = yi/R[i+i*n];
    }
}

// Test dense Cholesky
void test_dense_cholesky()
{
    double A[36], b[6];
    get_Aref(A);
    get_bref(b);

    dense_cholesky(A, 6);
    cholesky_solve(A, b, 6);
    printf("Check that dense Cholesky works: %g\n",
           check_solution(b));    
}

/**
## Dense storage band solver

For this version, we use the standard dense column-major storage format
for the matrix and its Cholesky factor, but without doing $O(n^3)$
arithmetic.  The key observation for band Cholesky is that if the
original matrix has bandwidth $b$ (i.e. at most $b$ superdiagonals
nonzero), then the Cholesky factor also has bandwidth $b$, and each Schur
complement step is affecting at most $b^2$ nonzeros.  The total cost for
band Cholesky is therefore $O(nb^2)$ rather than $O(n^3)$.
 */

 // Compute Cholesky of n-by-n dense A with bandwidth bw
void band_cholesky0(double* A, int n, int bw)
{
    for (int k = 0; k < n; ++k) {

        // Compute kth diagonal element
        A[k+n*k] = sqrt(A[k+n*k]);

        // Scale across the row
        for (int j = k+1; j < n && j <= k+bw; ++j)
            A[k+n*j] /= A[k+n*k];

        // Apply the Schur complement update
        for (int j = k+1; j < n && j <= k+bw; ++j)
            for (int i = k+1; i <= j; ++i)
                A[i+n*j] -= A[k+n*i]*A[k+n*j];
    }
}

// Overwrite input variable x with R \ (R^T \ x)
void bcholesky_solve0(double* R, double* x, int n, int bw)
{
    // Forward substitution
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int dj = 1; dj <= bw && dj <= i; ++dj)
            bi -= R[(i-dj)+i*n]*x[(i-dj)];
        x[i] = bi/R[i+i*n];
    }

    // Backward substitution
    for (int i = n-1; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j <= i+bw && j < n; ++j)        
            yi -= R[i+j*n]*x[j];
        x[i] = yi/R[i+i*n];
    }
}

// Test band Cholesky
void test_band_cholesky0()
{
    double A[36], b[6];
    get_Aref(A);
    get_bref(b);

    band_cholesky0(A, 6, 2);
    bcholesky_solve0(A, b, 6, 2);
    printf("Check that band Cholesky (dense format) works: %g\n",
           check_solution(b));    
}

/**
## Packed storage

Before discussing band Cholesky, we need to discuss the band
storage format.  Because we are dealing with symmetric matrices,
we only explicitly store the entries of the upper triangle in
this case.  For an $$-by-$n$ matrix $A$ with bandwidth $b$,
we store the entries in a packed array $P$ of size $n$-by-$b$,
where each column of $P$ represents a diagonal of $A$ (starting
from the main diagonal).  In terms of indices, we have that
$P_{j,d} = A_{j-d,j}$ represents the element of diagonal $d$
in column $j$ (which means that any but the main diagonal will
start with some "don't care spaces").  Equivalently, we can write
that $A_{i,j}$ maps to position $P_{j,j-i}$.

The `dense_to_band` function converts from dense format to band format,
while `print_dense` and `print_band` print matrices in the two formats.
The tester outputs the following comparison of the two:

         A in dense format:
             5.61   0.457    1.56       0       0       0
            0.457    4.76     1.4   0.314       0       0
             1.56     1.4    5.69    1.02    1.06       0
                0   0.314    1.02     5.7    1.51    1.83
                0       0    1.06    1.51    5.79   0.876
                0       0       0    1.83   0.876    4.26
         Compare to band format:
             5.61
             4.76   0.457
             5.69     1.4    1.56
              5.7    1.02   0.314
             5.79    1.51    1.06
             4.26   0.876    1.83
 */

// Convert dense n-by-n A to band matrix P with bandwidth bw
void dense_to_band(double* A, double* P, int n, int bw)
{
    for (int d = 0; d <= bw; ++d)
        for (int j = d; j < n; ++j) {
            int i = j-d;
            P[j+d*n] = A[i+j*n];
        }
}

// Print dense n-by-n A
void print_dense(double* A, int n)
{
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j)
            printf("  % 6.3g", A[i+j*n]);
        printf("\n");
    }
}

// Print band format array P (n-by-nw)
void print_band(double* PA, int n, int bw)
{
    for (int i = 0; i < n; ++i) {
        for (int d = 0; d <= bw && d <= i; ++d)
            printf("  % 6.3g", PA[i+d*n]);
        printf("\n");
    }
}

// Test conversion and print
void test_dense_to_band()
{
    double A[36], PA[18];
    get_Aref(A);
    dense_to_band(A, PA, 6, 2);    
    printf("A in dense format:\n");
    print_dense(A, 6);
    printf("Compare to band format:\n");
    print_band(PA, 6, 2);    
}

/**
## Band storage Cholesky

The band storage Cholesky solver uses the exact same algorithm as the 
band Cholesky algorithm in dense format, except that it uses the indexing
for the band storage scheme in lieu of the indexing for the dense storage.
*/

 // Compute Cholesky of n-by-n packed A with bandwidth bw
void band_cholesky(double* PA, int n, int bw)
{
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

// Overwrite input variable x with R \ (R^T \ x)
void bcholesky_solve(double* PR, double* x, int n, int bw)
{
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

void test_band_cholesky()
{
    double A[36], PA[18], b[6];
    get_Aref(A);
    get_bref(b);
    dense_to_band(A, PA, 6, 2);
    band_cholesky(PA, 6, 2);
    bcholesky_solve(PA, b, 6, 2);
    printf("Check that band Cholesky in band storage works: %g\n",
           check_solution(b));    
}

/**
As an additional sanity check, we make sure that the reference
Cholesky and the band Cholesky are the same.
*/
void compare_choleskys()
{
    double A[36], PA[18], PR[18];
    get_Aref(A);
    dense_to_band(A, PA, 6, 2);
    band_cholesky(PA, 6, 2);
    dense_cholesky(A, 6);
    dense_to_band(A, PR, 6, 2);

    double r = 0.0;
    int bw = 2, n = 6;
    for (int d = 0; d <= bw; ++d)
        for (int j = d; j < n; ++j) {
            double x = PA[j+d*n]-PR[j+d*n];
            r += x*x;
        }
    r = sqrt(r);
    printf("Compare Cholesky factorizations: %g\n", r);
}

/**
## Main routine
*/
int main()
{
    printf("=== Band demo ===\n");
    test_check_solution();
    test_dense_cholesky();
    test_band_cholesky0();
    test_dense_to_band();
    test_band_cholesky();
    compare_choleskys();
    return 0;
}
