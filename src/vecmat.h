#ifndef VECMAT_H
#define VECMAT_H

//ldoc on
/**
 * # Vector and matrix conveniences
 * 
 * We define a structure `vecmat_t` consisting of dimension/sparsity data
 * followed by a data array.  A `vecmat_t` can represent a dense matrix,
 * banded matrix, sparse matrix (in various formats).  The `vecmat_t` doesn't
 * tell you which representation it's in, you just have to know from context.
 * All representations must store all their nonzero elements in the `data` array,
 * and no two slots in the `data` array can represent the same (i,j) matrix element.
 * 
 * Therefore "clear" (set to zeros without changing sparsity structure)
 * and Frobenius norm can be done generically.
 */

typedef struct vecmat_t {
    int len;       // length of data array
    int m,n;       // representation-specific data, e.g. but not necessarily number of rows, cols
    int *ind1, *ind2;  // indexing arrays for sparse matrices, if needed, otherwise NULL
    double data[1]; // Start of data array
} vecmat_t;

// Create and free 
vecmat_t* malloc_vecmat(int len);
void free_vecmat(vecmat_t* vecmat);

vecmat_t* dense_malloc_vecmat(int m, int n);

// Clear storage
void vecmatn_clear(double* data, int len);
void vecmat_clear(vecmat_t* data);

// Print array (assumes column major order)
void dense_vecmatn_print(double* data, int m, int n);
void dense_vecmat_print(vecmat_t* data);

// Cholesky factorization and solve (uses only upper triangular)
void dense_vecmatn_cfactor(double* A, int n);
void dense_vecmatn_csolve(double* R, double* x, int n);
void dense_vecmat_cfactor(vecmat_t* A);
void dense_vecmat_csolve(vecmat_t* R, double* x);

// LU factorization and solve
void dense_vecmatn_lufactor(int* ipiv, double* A, int n);
void dense_vecmatn_lusolve(int* ipiv, double* A, double* x, int n);
void dense_vecmatn_lusolveT(int* ipiv, double* A, double* x, int n);
void dense_vecmat_lufactor(int* ipiv, vecmat_t* A);
void dense_vecmat_lusolve(int* ipiv, vecmat_t* A, double* x);
void dense_vecmat_lusolveT(int* ipiv, vecmat_t* A, double* x);

// Jacobian determinant from LU factorization
double dense_vecmatn_lujac(int* ipiv, double* A, int n);
double dense_vecmat_lujac(int* ipiv, vecmat_t* A);

// Squared norm and norm computations
double vecmatn_norm2(double* data, int len);
double vecmatn_norm(double* data, int len);
double vecmat_norm2(vecmat_t* data);
double vecmat_norm(vecmat_t* data);

//ldoc off
#endif /* VECMAT_H */
