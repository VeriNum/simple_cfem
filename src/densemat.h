#ifndef DENSEMAT_H
#define DENSEMAT_H

#include "alloc.h"

//ldoc on
/**
 * # Vector and matrix conveniences
 * 
 * To represent a dense matrix, we define a structure `densemat_t` consisting of 
 * dimensions followed by a data array.  
 */

typedef struct densemat_t {
    int m,n;  // rows, columns
    double data[0];  // Start of data array
} *densemat_t;

// Create and free 
densemat_t densemat_malloc(int m, int n);
void densemat_free(densemat_t dm);

// Clear storage
void densematn_clear(double* data, int m, int n);
void densemat_clear(densemat_t dm);

// Print array (assumes column major order)
void densematn_print(double* data, int m, int n);
void densemat_print(densemat_t data);

// Cholesky factorization and solve (uses only upper triangular)
void densematn_cfactor(double* A, int n);
void densematn_csolve(double* R, double* x, int n);
void densemat_cfactor(densemat_t A);
void densemat_csolve(densemat_t R, double* x);

// LU factorization and solve
void densematn_lufactor(int* ipiv, double* A, int n);
void densematn_lusolve(int* ipiv, double* A, double* x, int n);
void densematn_lusolveT(int* ipiv, double* A, double* x, int n);
void densemat_lufactor(int* ipiv, densemat_t A);
void densemat_lusolve(int* ipiv, densemat_t A, double* x);
void densemat_lusolveT(int* ipiv, densemat_t A, double* x);

// Jacobian determinant from LU factorization
double densematn_lujac(int* ipiv, double* A, int n);
double densemat_lujac(int* ipiv, densemat_t A);

// Squared norm and norm computations
double data_norm2(double* data, int n);
double data_norm(double* data, int n);
double densemat_norm2(densemat_t dm);
double densemat_norm(densemat_t dm);

// Accessor/setter functions for column-major indexing
double densemat_get(densemat_t dm, int i, int j);
void densemat_set(densemat_t dm, int i, int j, double x);
void densemat_addto(densemat_t dm, int i, int j, double x);

//ldoc off
#endif /* DENSEMAT_H */
