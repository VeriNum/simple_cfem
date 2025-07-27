#include <stdio.h>
#include <assert.h>

#include "assemble.h"
#include "vecmat.h"
#include "bandmat.h"

/**
 * ### Implementation
 * 
 */
// Wrappers to call assembler add/clear methods
void assemble_add(assemble_t* assembler, double* emat, int* ids, int ne)
{
    (*(assembler->add))(assembler->p, emat, ids, ne);
}

void assemble_clear(assemble_t* assembler)
{
    (*(assembler->clear))(assembler->p);
}

/**
 * Setting up an assembler object just involves initializing the
 * data pointer `p` and setting up the method table.  Note that
 * both the dense and band storage sit on top of our `vecmat_t` array
 * manager, so we can use the same `clear` implementation in both cases.
 * 
 */
// Declare private implementations for the methods
static void assemble_dense_add(void* p, double* emat, int* ids, int ne);
static void assemble_bandmat_add(void* p, double* emat, int* ids, int ne);
static void assemble_vecmat_clear(void* p);

// Initialize a dense assembler
void init_assemble_dense(assemble_t* assembler, double* A)
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

/**
 * The assembly loops logically execute
 * 
 *     A[iglobal, jglobal] += Ae[i, j]
 *
 * for every local index pair `(i,j)`.  We filter out the contributions
 * where the global indices are negative (indicating that these
 * contributions are not needed because of an essential boundary condition.
 *
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

/**
 * Clearing the storage is blessedly trivial.
 * 
 */
static void assemble_vecmat_clear(void* p)
{
    vecmat_clear((double*) p);
}

/**
 * Finally, we also need vector assembly.
 * 
 */
void assemble_vector(double* v, double* ve, int* ids, int ne)
{
    for (int ie = 0; ie < ne; ++ie) {
        int i = ids[ie];
        if (i >= 0)
            v[i] += ve[ie];
    }
}
