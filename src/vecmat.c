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
 * The `malloc_vecmat` function allocates space for the head structure
 * (which contains the first entry in the data array) along with space
 * for the remainder of the `m*n` double precision numbers in the data array.  
 */
vecmat_t* malloc_vecmat(int len)
{
    vecmat_t* h = malloc(sizeof(vecmat_t) + (len-1)*sizeof(double));
    h->len= len;
    h->ind1= NULL;
    h->ind2= NULL;
    return h;
}

vecmat_t* dense_malloc_vecmat(int m, int n)
{ vecmat_t *vm = malloc_vecmat(m*n);
  vm->m=m; vm->n=n;
  return vm;
}

void free_vecmat(vecmat_t* vm)
{
    free(vm->ind1);
    free(vm->ind2);
    free(vm);
}

void vecmatn_clear(double* data, int len)
{
    memset(data, 0, len * sizeof(double));
}

void vecmat_clear(vecmat_t* vm)
{
    vecmatn_clear(vm->data, vm->len);
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
void dense_vecmatn_print(double* data, int m, int n)
{
    printf("%d-by-%d\n", m, n);
    for (int i = 0; i < m; ++i) {
        for (int j = 0; j < n; ++j)
            printf(" % 6.2g", data[i+j*m]);
        printf("\n");
    }
}

void dense_vecmat_print(vecmat_t* vm)
{
    dense_vecmatn_print(vm->data, vm->m, vm->n);
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
void dense_vecmatn_cfactor(double* A, int n)
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
void dense_vecmat_cfactor(vecmat_t* A)
{
    assert(A->m == A->n);
    dense_vecmatn_cfactor(A->data, A->m);
}

//ldoc on
/**
 * The `vecmat_csolve(R, x)` function assumes a Cholesky factor in the
 * upper triangle of input argument `R`; the argument `x` is the
 * right-hand side vector $b$ on input, and the solution vector $x$ on
 * output.
 */
void dense_vecmatn_csolve(double* R, double* x, int n)
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
void dense_vecmat_csolve(vecmat_t* R, double* x)
{
    dense_vecmatn_csolve(R->data, x, R->n);
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
void dense_vecmatn_lufactor(int* ipiv, double* A, int n)
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
void dense_vecmatn_lusolve(int* ipiv, double* A, double* x, int n)
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
void dense_vecmatn_lusolveT(int* ipiv, double* A, double* x, int n)
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
double dense_vecmatn_lujac(int* ipiv, double* A, int n)
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

void dense_vecmat_lufactor(int* ipiv, vecmat_t* A)
{
    assert(A->m == A->n);
    dense_vecmatn_lufactor(ipiv, A->data, A->m);
}

void dense_vecmat_lusolve(int* ipiv, vecmat_t* A, double* x)
{
    dense_vecmatn_lusolve(ipiv, A->data, x, A->m);
}

void dense_vecmat_lusolveT(int* ipiv, vecmat_t* A, double* x)
{
    dense_vecmatn_lusolveT(ipiv, A->data, x, A->m);
}

double dense_vecmat_lujac(int* ipiv, vecmat_t* A)
{
    return dense_vecmatn_lujac(ipiv, A->data, A->m);
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
double vecmatn_norm2(double* data, int len)
{
    double result = 0.0;
    for (int j = 0; j < len; ++j) {
        double xj = data[j];
        result += xj*xj;
    }
    return result;
}

double vecmatn_norm(double* data, int len)
{
    return sqrt(vecmatn_norm2(data, len));
}

//ldoc off
double vecmat_norm2(vecmat_t* vm)
{
    return vecmatn_norm2(vm->data, vm->len);
}

double vecmat_norm(vecmat_t* vm)
{
    return vecmatn_norm(vm->data, vm->len);
}
