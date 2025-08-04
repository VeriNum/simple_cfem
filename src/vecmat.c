#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>

#include "vecmat.h"

//ldoc on
/**
 * ## Memory management
 * 
 * We usually refer to a `vecmat_t` with a pointer to the (extended)
 * `data` array whose start is declared in the `vecmat_head_t` structure.
 * The `vecmat` function takes a double precision pointer to such a
 * data field and backs up to get a pointer to the struct.
 */
vecmat_head_t* vecmat(double* data)
{
    vecmat_head_t dummy;
    void* p = (char*) data + ((char*) &dummy - (char*) dummy.data);
    return (vecmat_head_t*) p;
}

/**
 * The `malloc_vecmat` function allocates space for the head structure
 * (which contains the first entry in the data array) along with space
 * for the remainder of the `m*n` double precision numbers in the data
 * array.  Because we want to be able to pass `vecmat_t` data into C
 * functions that take plain pointers, we don't return the pointer to
 * the head structure, but the pointer to the data field.
 */
double* malloc_vecmat(int m, int n)
{
    vecmat_head_t* h = malloc(sizeof(vecmat_head_t) + (m*n-1)*sizeof(double));
    h->m = m;
    h->n = n;
    return h->data;
}

void free_vecmat(double* data)
{
    free(vecmat(data));
}

void vecmatn_clear(double* data, int m, int n)
{
    memset(data, 0, m*n * sizeof(double));
}

void vecmat_clear(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    vecmatn_clear(data, vm->m, vm->n);
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
void vecmatn_print(double* data, int m, int n)
{
    printf("%d-by-%d\n", m, n);
    for (int i = 0; i < m; ++i) {
        for (int j = 0; j < n; ++j)
            printf(" % 6.2g", data[i+j*m]);
        printf("\n");
    }
}

void vecmat_print(double* data)
{
    vecmat_head_t* vm = vecmat(data);    
    vecmatn_print(data, vm->m, vm->n);
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
 * We will not bother to show the wrapper around the `vecmatn` version.
 */
void vecmatn_cfactor(double* A, int n)
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
void vecmat_cfactor(double* A)
{
    vecmat_head_t* vm = vecmat(A);
    assert(vm->m == vm->n);
    vecmatn_cfactor(A, vm->m);
}

//ldoc on
/**
 * The `vecmat_csolve(R, x)` function assumes a Cholesky factor in the
 * upper triangle of input argument `R`; the argument `x` is the
 * right-hand side vector $b$ on input, and the solution vector $x$ on
 * output.
 */
void vecmatn_csolve(double* R, double* x, int n)
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
void vecmat_csolve(double* R, double* x)
{
    vecmat_head_t* vm = vecmat(R);
    vecmatn_csolve(R, x, vm->n);
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
void vecmatn_lufactor(int* ipiv, double* A, int n)
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
 * The `vecmat_lusolve` function assumes that the factorization has
 * already been computed.  On input, `x` represents $b$; on output,
 * `x` represents $x = A^{-1} b$.
 */
void vecmatn_lusolve(int* ipiv, double* A, double* x, int n)
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
 * The `vecmat_lusolveT` variant solves a linear system $A^T x = b$ where
 * $A^T = U^T L^T P$
 */
void vecmatn_lusolveT(int* ipiv, double* A, double* x, int n)
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
double vecmatn_lujac(int* ipiv, double* A, int n)
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
 * We don't bother including the `vecmat_t` callthroughs in the
 * autodoc output.
 */

void vecmat_lufactor(int* ipiv, double* A)
{
    vecmat_head_t* vm = vecmat(A);
    assert(vm->m == vm->n);
    vecmatn_lufactor(ipiv, A, vm->m);
}

void vecmat_lusolve(int* ipiv, double* A, double* x)
{
    vecmat_head_t* vm = vecmat(A);
    vecmatn_lusolve(ipiv, A, x, vm->m);
}

void vecmat_lusolveT(int* ipiv, double* A, double* x)
{
    vecmat_head_t* vm = vecmat(A);
    vecmatn_lusolveT(ipiv, A, x, vm->m);
}

double vecmat_lujac(int* ipiv, double* A)
{
    vecmat_head_t* vm = vecmat(A);
    return vecmatn_lujac(ipiv, A, vm->m);
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
double vecmatn_norm2(double* data, int n)
{
    double result = 0.0;
    for (int j = 0; j < n; ++j) {
        double xj = data[j];
        result += xj*xj;
    }
    return sqrt(result);
}

double vecmatn_norm(double* data, int n)
{
    return sqrt(vecmatn_norm2(data, n));
}

//ldoc off
double vecmat_norm2(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    return vecmatn_norm2(data, vm->m * vm->n);
}

double vecmat_norm(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    return vecmatn_norm(data, vm->m * vm->n);
}
