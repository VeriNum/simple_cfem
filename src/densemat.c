#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>

#include "densemat.h"

//ldoc on
/**
 * ## Memory management
 *
 * The `densemat_malloc` function allocates space for the head structure
 * (which contains the first entry in the data array) along with space
 * for the remainder of the `m*n` double precision numbers in the data array.  
 */
densemat_t* densemat_malloc(int m, int n)
{
    densemat_t* h = surely_malloc(sizeof(densemat_t) + (m*n)*sizeof(double));
    h->m=m;
    h->n=n;
    return h;
}

void densemat_free(densemat_t* vm)
{
    free(vm);
}

void densematn_clear(double* data, int m, int n)
{
  memset(data, 0, (m*n) * sizeof(double));
}

void densemat_clear(densemat_t* vm)
{
  densematn_clear(vm->data, vm->m, vm->n);
}

/**
 * ## I/O
 * 
 * We provide a print routines as an aid to debugging.  In order
 * to make sure that modest size matrices can be printed on the
 * screen in a digestible matter, we only print the first couple
 * digits in each entry.  Note that we assume column major layout
 * throughout.
 */
void densematn_print(double* data, int m, int n)
{
    printf("%d-by-%d\n", m, n);
    for (int i = 0; i < m; ++i) {
        for (int j = 0; j < n; ++j)
            printf(" % 6.2g", data[i+j*m]);
        printf("\n");
    }
}

void densemat_print(densemat_t* vm)
{
    densematn_print(vm->data, vm->m, vm->n);
}

/**
 * ## Cholesky factorization
 * 
 * For our finite element code, we will largely work with SPD matrices
 * for which a Cholesky solve is appropriate.  On input, we assume a column
 * major representation in which the upper triangle represents the upper
 * triangle of an SPD matrix; the lower triangle is ignored.  On output,
 * the upper triangle of the matrix argument is overwritten by the
 * Cholesky factor.  We will error out if we encounter a negative diagonal
 * (in violation of the assumed positive definiteness).
 * 
 * We will not bother to show the wrapper around the `densematn` version.
 */
void densematn_cfactor(double* A, int n)
{
    for (int k = 0; k < n; ++k) {

        // Compute kth diagonal element
        double akk = A[k+n*k];
        assert(akk >= 0.0);
        double rkk = sqrt(akk);
        A[k+n*k] = rkk;

        // Scale across the row
        for (int j = k+1; j < n; ++j)
            A[k+n*j] /= rkk;

        // Apply the Schur complement update
        for (int j = k+1; j < n; ++j)
            for (int i = k+1; i <= j; ++i)
                A[i+j*n] -= A[k+i*n]*A[k+j*n];
    }
}

//ldoc off
void densemat_cfactor(densemat_t* A)
{
    assert(A->m == A->n);
    densematn_cfactor(A->data, A->m);
}

//ldoc on
/**
 * The `densemat_csolve(R, x)` function assumes a Cholesky factor in the
 * upper triangle of input argument `R`; the argument `x` is the
 * right-hand side vector $b$ on input, and the solution vector $x$ on
 * output.
 */
void densematn_csolve(double* R, double* x, int n)
{
    // Forward substitution
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int j = 0; j < i; ++j)
            bi -= R[j+i*n]*x[j];
        x[i] = bi/R[i+i*n];
    }

    // Backward substitution
    for (int i = n; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j < n; ++j)
            yi -= R[i+n*j]*x[j];
        x[i] = yi/R[i+i*n];
    }
}

//ldoc off
void densemat_csolve(densemat_t* R, double* x)
{
    densematn_csolve(R->data, x, R->n);
}

//ldoc on
/**
 * ## LU factorization and solve
 * 
 * Even if the system matrices in a finite element code are SPD, the
 * Jacobians that are used in mapped elements generally will not be.
 * Therefore, we need a basic pivoted LU factorization along with the basic
 * Cholesky.
 * 
 * The factorization routine overwrites `A` with the $L$ and $U$ factors,
 * packed into the (strictly) lower and the upper triangular parts of $A$.
 * The pivot vector is stored in `ipiv`, where `ipiv[i] = l` implies that
 * rows $i$ and $l$ were swapped at step $i$ of the elimination.
 */
void densematn_lufactor(int* ipiv, double* A, int n)
{
    for (int j = 0; j < n; ++j) {

        // Find pivot row
        int ipivj = j;
        for (int i = j+1; i < n; ++i)
            if (fabs(A[i+n*j]) > fabs(A[ipivj+n*j]))
                ipivj = i;
        ipiv[j] = ipivj;

        // Apply row swap, if needed
        if (ipivj != j)
            for (int k = j; k < n; ++k) {
                double t = A[j+n*k];
                A[j+n*k] = A[ipivj+n*k];
                A[ipivj+n*k] = t;
            }

        // Compute multipliers
        double Ujj = A[j+j*n];
        for (int i = j+1; i < n; ++i)
            A[i+j*n] /= Ujj;

        // Apply Schur complement update
        for (int k = j+1; k < n; ++k) {
            double Ujk = A[j+k*n];
            for (int i = j+1; i < n; ++i) {
                double Lij = A[i+j*n];
                A[i+k*n] -= Lij*Ujk;
            }
        }
    }
}

/**
 * The `densemat_lusolve` function assumes that the factorization has
 * already been computed.  On input, `x` represents $b$; on output,
 * `x` represents $x = A^{-1} b$.
 */
void densematn_lusolve(int* ipiv, double* A, double* x, int n)
{
    // Apply P
    for (int i = 0; i < n; ++i)
        if (ipiv[i] != i) {
            double t = x[i];
            x[i] = x[ipiv[i]];
            x[ipiv[i]] = t;
        }

    // Forward substitution
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int j = 0; j < i; ++j)
            bi -= A[i+j*n]*x[j];
        x[i] = bi;
    }

    // Backward substitution
    for (int i = n; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j < n; ++j)
            yi -= A[i+n*j]*x[j];
        x[i] = yi/A[i+i*n];
    }
}

/**
 * The `densemat_lusolveT` variant solves a linear system $A^T x = b$ where
 * $A^T = U^T L^T P$
 */
void densematn_lusolveT(int* ipiv, double* A, double* x, int n)
{
    // Forward substitution (with U^T)
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int j = 0; j < i; ++j)
            bi -= A[j+i*n]*x[j];
        x[i] = bi/A[i+i*n];
    }
    
    // Backward substitution (with L^T)
    for (int i = n; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j < n; ++j)
            yi -= A[j+n*i]*x[j];
        x[i] = yi;
    }

    // Apply P^T
    for (int i = n-1; i >= 0; --i)
        if (ipiv[i] != i) {
            double t = x[i];
            x[i] = x[ipiv[i]];
            x[ipiv[i]] = t;
        }
}

/**
 * The Jacobian determinant can be computed from the product of the
 * diagonals of $U$ times the sign of the permutation matrix (given by
 * the parity of the number of swaps in the factored permutation).
 */
double densematn_lujac(int* ipiv, double* A, int n)
{
    double J = 1.0;
    int nswap = 0;
    for (int i = 0; i < n; ++i) {
        if (ipiv[i] != i)
            ++nswap;
        J *= A[i+i*n];
    }
    return (nswap % 2 == 0) ? J : -J;
}

//ldoc off
/**
 * We don't bother including the `densemat_t` callthroughs in the
 * autodoc output.
 */

void densemat_lufactor(int* ipiv, densemat_t* A)
{
    assert(A->m == A->n);
    densematn_lufactor(ipiv, A->data, A->m);
}

void densemat_lusolve(int* ipiv, densemat_t* A, double* x)
{
    densematn_lusolve(ipiv, A->data, x, A->m);
}

void densemat_lusolveT(int* ipiv, densemat_t* A, double* x)
{
    densematn_lusolveT(ipiv, A->data, x, A->m);
}

double densemat_lujac(int* ipiv, densemat_t* A)
{
    return densematn_lujac(ipiv, A->data, A->m);
}

//ldoc on
/**
 * ## Norm computations
 * 
 * Just for checking on residuals and errors, it's convenient to have
 * some functions for computing the squared Euclidean norm and the
 * norm of a vector.  We assume that things are sufficiently well scaled
 * that we don't need to worry about over/underflow.
 */
double data_norm2(double* data, int n)
{
    double result = 0.0;
    for (int j = 0; j < n; ++j) {
        double xj = data[j];
        result += xj*xj;
    }
    return result;
}

double data_norm(double* data, int n)
{
    return sqrt(data_norm2(data, n));
}

double densemat_norm2(densemat_t* vm)
{
    return data_norm2(vm->data, vm->m*vm->n);
}

double densemat_norm(densemat_t* vm)
{
    return data_norm(vm->data, vm->m*vm->n);
}
