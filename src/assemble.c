#include <stdio.h>
#include <assert.h>

#include "assemble.h"
#include "vecmat.h"
#include "bandmat.h"

/*
 * Private implementations
 */

// Add to a dense matrix
static void assemble_dense_add(void* p, double* emat, int* ids, int ne)
{
    vecmat_head_t* head = vecmat(p);
    double* A = head->data;
    int n = head->m;

    for (int je = 0; je < ne; ++je) {
        int j = ids[je];
        for (int ie = 0; ie <= je; ++ie) {
            int i = ids[ie];
            if (i >= 0 && j >= i)
                A[i+n*j] += emat[ie+ne*je];
        }
    }
}

// Add to band matrix
static void assemble_bandmat_add(void* p, double* emat, int* ids, int ne)
{
    vecmat_head_t* head = vecmat(p);
    double* P = head->data;
    int n = head->m;
    int b = head->n-1;

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

static void assemble_vecmat_clear(void* p)
{
    vecmat_clear((double*) p);
}

/*
 * Public interface routines
 */

// Initialize a dense assembler
void init_assembler_dense(assemble_t* assembler, double* A)
{
    assembler->p = A;
    assembler->add = assemble_dense_add;
    assembler->clear = assemble_vecmat_clear;
}

// Initialize a band assembler
void init_assemble_band(assemble_t* assembler, double* b)
{
    assembler->p = b;
    assembler->add = assemble_bandmat_add;
    assembler->clear = assemble_vecmat_clear;
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
