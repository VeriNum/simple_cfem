#ifndef ASSEMBLE_H
#define ASSEMBLE_H
#include <densemat.h>
#include <bandmat.h>

//ldoc on
/**
 * # Matrix interface
 * 
 * There are several matrix formats that we might want to use for
 * solving the linear systems that arise from FEM problems.
 * These include dense storage, banded storage, coordinate form, or CSR.  
 * Because we would like
 * to re-use the same FEM logic with these different formats,
 * we define an abstract `assemble_t` interface with two basic methods:
 * 
 * - `add(assembler, i,j, x)` adds value x to the matrix component at (i,j)
 * - `clear(assembler)` sets the matrix to zero, preserving the
 *   sparsity pattern ("graph").
 * 
 */

// Interface for general assembler object (callback + context)
typedef struct matrix_data_t *matrix_data_t;

typedef struct matrix_t {
    matrix_data_t p;                            // Context
  void (*add)(matrix_data_t, int, int, double); // Add contribution
    void (*clear)(matrix_data_t); // set to zero
    double (*norm2)(matrix_data_t); // square of Frobenius norm
    void (*print)(matrix_data_t);
} *matrix_t;

// Convenience functions that call the matrix methods
void matrix_add(matrix_t m, int i, int j, double x);
void matrix_clear(matrix_t m);
double matrix_norm2(matrix_t m);
void matrix_print(matrix_t m);

/**
 * We currently only support two types of matrixrs: dense and band.
 * In all cases, we assume that the dimension `n` of the matrix
 * is big enough (all active indices are less than `n`).  For the
 * band matrix, we do NOT check to make sure there are no contributions
 * that are outside the band; it's up to the client to establish that precondition.
 */
void init_matrix_dense(matrix_t m, densemat_t A);
void init_matrix_band(matrix_t m, bandmat_t b);

//ldoc off
#endif /* ASSEMBLE_H */
