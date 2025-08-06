#include <stdio.h>
#include <math.h>
#include <assert.h>

#include "assemble.h"
#include "densemat.h"
#include "bandmat.h"

//ldoc on
/**
 * ## Method dispatch
 */
void assemble_add(assemble_t* assembler, double* emat, int* ids, int ne)
{
    (*(assembler->add))(assembler->p, emat, ids, ne);
}

void assemble_clear (assemble_t *assembler)
{
    (*(assembler->clear))(assembler->p);
}

double assemble_norm2 (assemble_t *assembler)
{
   return (*(assembler->norm2))(assembler->p);
}

double assemble_norm (assemble_t *assembler) {
  return sqrt(assemble_norm2(assembler));
}

void assemble_print (assemble_t *assembler)
{
    (*(assembler->print))(assembler->p);
}



/**
 * Setting up an assembler object just involves initializing the
 * data pointer `p` and setting up the method table.  
 * 
 */
// Declare private implementations for the methods
/*static*/ void assemble_dense_add(assemble_data_t* p, double* emat, int* ids, int ne);
/*static*/ void assemble_bandmat_add(assemble_data_t* p, double* emat, int* ids, int ne);

// Initialize a dense assembler
void init_assemble_dense(assemble_t* assembler, densemat_t* A)
{
    assembler->p = (assemble_data_t*)A;
    assembler->add = assemble_dense_add;
    assembler->clear = (void (*)(densemat_t*))densemat_clear;
    assembler->norm2 = (double (*)(densemat_t*))densemat_norm2;
    assembler->print = (void (*)(densemat_t*))densemat_print;
}

// Initialize a band assembler
void init_assemble_band(assemble_t* assembler, bandmat_t* b)
{
    assembler->p = (assemble_data_t*)b;
    assembler->add = assemble_bandmat_add;
    assembler->clear = (void (*)(bandmat_t*))bandmat_clear;
    assembler->norm2 = (double (*)(bandmat_t*))bandmat_norm2;
    assembler->print = (void (*)(bandmat_t*))bandmat_print;
}

/**
 * ## Matrix assembly loops
 * 
 * The assembly loops logically execute `A[iglobal, jglobal] += Ae[i, j]`
 * for every local index pair `(i,j)`.  We filter out the contributions
 * where the global indices are negative (indicating that these
 * contributions are not needed because of an essential boundary condition.
 */
/*static*/ void assemble_dense_add(assemble_data_t* p, double* emat, int* ids, int ne)
{
    densemat_t *A = (densemat_t*)p;
    int n = A->m;

    for (int je = 0; je < ne; ++je) {
        int j = ids[je];
        for (int ie = 0; ie <= je; ++ie) {
            int i = ids[ie];
            if (i >= 0 && j >= i)
                A->data[i+n*j] += emat[ie+ne*je];
        }
    }
}

/*static*/ void assemble_bandmat_add(assemble_data_t* p, double* emat, int* ids, int ne)
{
    bandmat_t *P = (bandmat_t *)p;
    int n = P->m;
    int b = P->b;

    for (int je = 0; je < ne; ++je) {
        int j = ids[je];
        for (int ie = 0; ie <= je; ++ie) {
            int i = ids[ie];
            int d = j-i;
            if (j >= 0 && d >= 0) {
                assert(d <= b);
                P->data[j+n*d] += emat[ie+ne*je];
            }
        }
    }
}

/**
 * ## Vector assembly
 */
void assemble_vector(double* v, double* ve, int* ids, int ne)
{
    for (int ie = 0; ie < ne; ++ie) {
        int i = ids[ie];
        if (i >= 0)
            v[i] += ve[ie];
    }
}
