#include <stdio.h>
#include <assert.h>

#include "assemble.h"
#include "bandmat.h"

/*
 * Private implementations
 */

// Add to band matrix
static void assemble_bandmat_add(void* p, double* emat, int* ids, int ne)
{
    bandmat_t* bm = (bandmat_t*) p;
    double* P = bm->P;
    int n = bm->n;
    int b = bm->b;

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

static void assemble_bandmat_clear(void* p)
{
    bandmat_clear((bandmat_t*) p);
}

/*
 * Public interface routines
 */

// Initialize a band assembler
void init_assemble_band(assemble_t* assembler, bandmat_t* b)
{
    assembler->p = b;
    assembler->add = assemble_bandmat_add;
    assembler->clear = assemble_bandmat_clear;
}

// Add a contribution to an assembler
void assemble_add(assemble_t* assembler, double* emat, int* ids, int ne)
{
    (*(assembler->add))(assembler->p, emat, ids, ne);
}

// Clear assembler
void assemble_clear(assemble_t* assembler)
{
    (*(assembler->clear))(assembler->p);
}

// Add to vector
void assemble_vector(double* v, double* ve, int* ids, int ne)
{
    for (int ie = 0; ie < ne; ++ie) {
        int i = ids[ie];
        if (i >= 0)
            v[i] += ve[ie];
    }
}
