#include <stdio.h>
#include <assert.h>

#include "assemble.h"
#include "bandmat.h"

/*
 * Private implementations
 */

// Add to band matrix
static void add_to_bandmat(void* p, double* emat, int* ids, int ne)
{
    bandmat_t* assembler = (bandmat_t*) p;
    double* P = assembler->P;
    int n = assembler->n;
    int b = assembler->b;

    for (int je = 0; je < ne; ++je) {
        int j = ids[je];
        for (int ie = 0; ie <= je; ++ie) {
            int i = ids[ie];
            int d = j-i;
            if (j >= 0 && d >= 0) {
                assert(d <= b);
                P[j+n*d] += emat[ie+ne*je];
            }
        }
    }
}

// Add to vector
static void add_to_vec(void* p, double* evec, int* ids, int ne)
{
    double* vec = (double*) p;
    for (int ie = 0; ie < ne; ++ie) {
        int i = ids[ie];
        if (i >= 0)
            vec[i] += evec[ie];
    }
}

/*
 * Public interface routines
 */

// Initialize a band assembler
void init_assemble_band(assemble_t* assembler, bandmat_t* b)
{
    assembler->p = b;
    assembler->add = add_to_bandmat;
}

// Initialize a vector assembler
void init_assemble_vec(assemble_t* assembler, double* v)
{
    assembler->p = v;
    assembler->add = add_to_vec;
}

// Add a contribution to an assembler
void assemble_add(assemble_t* assembler, double* emat, int* ids, int ne)
{
    (*(assembler->add))(assembler->p, emat, ids, ne);
}
