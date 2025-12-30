#include <stdio.h>
#include <math.h>
#include <assert.h>

#include "assemble.h"
#include <densemat.h>
#include <bandmat.h>

//ldoc on
/**
 * ## Method dispatch
 */
void assemble_add(assemble_t assembler, int i, int j, double x) {
  (*(assembler->add))(assembler->p, i, j, x);
}

void assemble_clear (assemble_t assembler) {
    (*(assembler->clear))(assembler->p);
}

double assemble_norm2 (assemble_t assembler) {
   return (*(assembler->norm2))(assembler->p);
}

double assemble_norm (assemble_t assembler) {
  return sqrt(assemble_norm2(assembler));
}

void assemble_print (assemble_t assembler) {
    (*(assembler->print))(assembler->p);
}



/**
 * Setting up an assembler object just involves initializing the
 * data pointer `p` and setting up the method table.  
 * 
 */

// Initialize a dense assembler
void casted_densemat_add(assemble_data_t p, int i, int j, double x) {
    densemat_addto((densemat_t)p,i,j,x);
}

void casted_densemat_clear(assemble_data_t p) {
  densemat_clear ((densemat_t)p);
}

double casted_densemat_norm2(assemble_data_t p) {
  return densemat_norm2 ((densemat_t)p);
}

void casted_densemat_print(assemble_data_t p) {
  densemat_print ((densemat_t)p);
}

void init_assemble_dense(assemble_t assembler, densemat_t A)
{
    assembler->p = (assemble_data_t)A;
    assembler->add = &casted_densemat_add;
    assembler->clear = &casted_densemat_clear;
    assembler->norm2 = &casted_densemat_norm2;
    assembler->print = &casted_densemat_print;
}

// Initialize a band assembler
void casted_bandmat_add(assemble_data_t p, int i, int j, double x) {
  /* TODO: fix bandmat_addto so that the j-i subtraction is done in there. */
    bandmat_addto((bandmat_t)p,j,j-i,x);
}

void casted_bandmat_clear(assemble_data_t p) {
  bandmat_clear ((bandmat_t)p);
}

double casted_bandmat_norm2(assemble_data_t p) {
  return bandmat_norm2 ((bandmat_t)p);
}

void casted_bandmat_print(assemble_data_t p) {
  bandmat_print ((bandmat_t)p);
}

void init_assemble_band(assemble_t assembler, bandmat_t b)
{
    assembler->p = (assemble_data_t)b;
    assembler->add = casted_bandmat_add;
    assembler->clear = casted_bandmat_clear;
    assembler->norm2 = casted_bandmat_norm2;
    assembler->print = casted_bandmat_print;
}

