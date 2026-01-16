#include <stdio.h>
#include <math.h>
#include <assert.h>

#include "matrix.h"
#include <densemat.h>
#include <bandmat.h>

//ldoc on
/**
 * ## Implementation of the Matrix-object module
 * ### Method dispatch
 */
void matrix_add(matrix_t m, int i, int j, double x) {
  (*(m->add))(m->p, i, j, x);
}

void matrix_clear (matrix_t m) {
    (*(m->clear))(m->p);
}

double matrix_norm2 (matrix_t m) {
   return (*(m->norm2))(m->p);
}

double matrix_norm (matrix_t m) {
  return sqrt(matrix_norm2(m));
}

void matrix_print (matrix_t m) {
    (*(m->print))(m->p);
}



/**
 * ### Setting up an matrix object 
 * just involves initializing the data pointer `p` and setting up the method table.  
 * 
 */

// Initialize a dense matrix
void casted_densemat_add(matrix_data_t p, int i, int j, double x) {
    densemat_addto((densemat_t)p,i,j,x);
}

void casted_densemat_clear(matrix_data_t p) {
  densemat_clear ((densemat_t)p);
}

double casted_densemat_norm2(matrix_data_t p) {
  return densemat_norm2 ((densemat_t)p);
}

void casted_densemat_print(matrix_data_t p) {
  densemat_print ((densemat_t)p);
}

void init_matrix_dense(matrix_t m, densemat_t A)
{
    m->p = (matrix_data_t)A;
    m->add = &casted_densemat_add;
    m->clear = &casted_densemat_clear;
    m->norm2 = &casted_densemat_norm2;
    m->print = &casted_densemat_print;
}

// Initialize a band matrix
void casted_bandmat_add(matrix_data_t p, int i, int j, double x) {
  /* TODO: fix bandmat_addto so that the j-i subtraction is done in there. */
    bandmat_addto((bandmat_t)p,j,j-i,x);
}

void casted_bandmat_clear(matrix_data_t p) {
  bandmat_clear ((bandmat_t)p);
}

double casted_bandmat_norm2(matrix_data_t p) {
  return bandmat_norm2 ((bandmat_t)p);
}

void casted_bandmat_print(matrix_data_t p) {
  bandmat_print ((bandmat_t)p);
}

void init_matrix_band(matrix_t m, bandmat_t b)
{
    m->p = (matrix_data_t)b;
    m->add = casted_bandmat_add;
    m->clear = casted_bandmat_clear;
    m->norm2 = casted_bandmat_norm2;
    m->print = casted_bandmat_print;
}

