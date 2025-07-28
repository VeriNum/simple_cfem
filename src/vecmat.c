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
    void* p = (void*) data + ((void*) &dummy - (void*) dummy.data);
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

void vecmat_clear(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    int m = vm->m, n = vm->n;
    memset(data, 0, m*n * sizeof(double));
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
void vecmat_print(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    int m = vm->m, n = vm->n;
    double* A = vm->data;
    printf("%d-by-%d\n", m, n);
    for (int i = 0; i < m; ++i) {
        for (int j = 0; j < n; ++j)
            printf(" % 6.2g", A[i+j*m]);
        printf("\n");
    }
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
 */
void vecmat_cfactor(double* A)
{
    vecmat_head_t* head = vecmat(A);
    int n = head->m;

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

/**
 * The `vecmat_csolve(R, x)` function assumes a Cholesky factor in the
 * upper triangle of input argument `R`; the argument `x` is the
 * right-hand side vector $b$ on input, and the solution vector $x$ on
 * output.
 */
void vecmat_csolve(double* R, double* x)
{
    vecmat_head_t* head = vecmat(R);
    int n = head->m;

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

/**
 * ## Norm computations
 * 
 * Just for checking on residuals and errors, it's convenient to have
 * some functions for computing the squared Euclidean norm and the
 * norm of a vector.  We assume that things are sufficiently well scaled
 * that we don't need to worry about over/underflow.
 */
double vecmat_norm2(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    int m = vm->m, n = vm->n;
    double* A = vm->data;
    double result = 0.0;
    for (int j = 0; j < n; ++j)
        for (int i = 0; i < m; ++i) {
            double Aij = A[i+j*m];
            result += Aij*Aij;
        }
    return sqrt(result);
}

double vecmat_norm(double* data)
{
    return sqrt(vecmat_norm2(data));
}
