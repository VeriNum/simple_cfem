#ifndef VECMAT_H
#define VECMAT_H

//ldoc on
/**
 * # Vector and matrix conveniences
 * 
 * C does not make it particularly easy to work with matrices and
 * vectors.  Part of the difficulty is the lack of a convenient place
 * to store size information.  We work around this by defining a data
 * structure (which we will refer to as a `vecmat_t`, though this type
 * is never explicitly used in our code) consisting of dimension data
 * followed by a data array.  We generally pass the object around with
 * a pointer to the start of the data (in standard C style), only
 * backing up in memory to access size information when we need it.
 */

typedef struct vecmat_head_t {
    int m, n;       // Row and column counts
    double data[1]; // Start of data array
} vecmat_head_t;

// Get header information by backing up from data pointer
vecmat_head_t* vecmat(double* data);

// Create and free 
double* malloc_vecmat(int m, int n);
void free_vecmat(double* data);

// Clear storage
void vecmat_clear(double* data);

// Print array (assumes column major order)
void vecmat_print(double* data);

// Cholesky factorization and solve (uses only upper triangular)
void vecmat_cfactor(double* A);
void vecmat_csolve(double* R, double* x);

// Squared norm and norm computations
double vecmat_norm2(double* data);
double vecmat_norm(double* data);

//ldoc off
#endif /* VECMAT_H */
