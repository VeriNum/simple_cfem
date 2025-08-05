#include <stdio.h>
#include <assert.h>

#include "assemble.h"
#include "vecmat.h"
#include "bandmat.h"

//ldoc on
/**
 * ## Method dispatch
 */
void assemble_add(assemble_t* assembler, double* emat, int* ids, int ne)
{
    (*(assembler->add))(assembler->p, emat, ids, ne);
}

/**
 * ## Generic clear
 */
void assemble_clear (assemble_t *assembler)
{
  vecmat_clear(assembler->p);
}

/**
 * Setting up an assembler object just involves initializing the
 * data pointer `p` and setting up the method table.  
 * 
 */
// Declare private implementations for the methods
/*static*/ void assemble_dense_add(vecmat_t* p, double* emat, int* ids, int ne);
/*static*/ void assemble_bandmat_add(vecmat_t* p, double* emat, int* ids, int ne);

// Initialize a dense assembler
void init_assemble_dense(assemble_t* assembler, vecmat_t* A)
{
    assembler->p = A;
    assembler->add = assemble_dense_add;
}

// Initialize a band assembler
void init_assemble_band(assemble_t* assembler, vecmat_t* b)
{
    assembler->p = b;
    assembler->add = assemble_bandmat_add;
}

/**
 * ## Matrix assembly loops
 * 
 * The assembly loops logically execute `A[iglobal, jglobal] += Ae[i, j]`
 * for every local index pair `(i,j)`.  We filter out the contributions
 * where the global indices are negative (indicating that these
 * contributions are not needed because of an essential boundary condition.
 */
/*static*/ void assemble_dense_add(vecmat_t* A, double* emat, int* ids, int ne)
{
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

/*static*/ void assemble_bandmat_add(vecmat_t* P, double* emat, int* ids, int ne)
{
    int n = P->m;
    int b = P->n-1;

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
