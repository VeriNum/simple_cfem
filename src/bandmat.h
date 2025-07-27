#ifndef BANDMAT_H
#define BANDMAT_H

//ldoc on
/**
 * ## Band matrix operations
 * 
 * We store symmetric band matrices using the LAPACK symmetric band
 * format (see, e.g. `DSBTRF`).  This is a packed storage format
 * in which a symmetric matrix with `b` nonzero diagonals off th
 * main diagonal in either direction is stored one diagonal at a time.
 * That is, the dense matrix entry `A[i,j]` (column major) is stored
 * in a packed array `P` of size `n`-by-`b+1` at location `P[j,d]`,
 * where `d = j-i` is the diagonal number.  The leading `d` entries
 * of diagonal `d` are not used (but we don't try to eliminate them
 * in the interest of keeping our indexing simple).  Because we are
 * interested in symmetric matrices, we only need to explicitly store
 * the upper triangle (`d >= 0`).
 * 
 * Because the storage format is essentially a dense `n`-by-`b+1`
 * array, we will not introduce a totally new data structure for the
 * band matrix; the `vecmat_t` storage container for dense matrices
 * that we introduced before works well enough.
 * 
 */
// Allocate a new bandmat (and maybe populate from a dense matrix)
double* malloc_bandmat(int n, int b);
double* dense_to_band(double* A, int n, int bw);

// Print a bandmat
void bandmat_print(double* PA);

// Cholesky and linear solve with Cholesky
void bandmat_factor(double* PA);
void bandmat_solve(double* PR, double* x);

//ldoc off
#endif /* BANDMAT_H */
