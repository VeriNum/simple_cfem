#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "alloc.h"
#include "matrix.h"
#include "element.h"
#include "bandmat.h"
#include "mesh.h"
#include "fem.h"

//ldoc on
/**
 * ## Implementation
 */
// Allocate mesh object
fem_t fem_malloc(mesh_t mesh, int ndof)
{
    int numnp = mesh->numnp;

    fem_t fe = surely_malloc(sizeof(struct fem_t));
    fe->mesh    = mesh;
    fe->etype   = NULL;
    fe->ndof    = ndof;
    fe->nactive = numnp * ndof;

    fe->U  = double_calloc(ndof * numnp);
    fe->F  = double_calloc(ndof * numnp);
    fe->id = int_calloc(ndof * numnp);

    return fe;
}

// Free mesh object
void fem_free(fem_t fe)
{
    free(fe->id);
    free(fe->F);
    free(fe->U);
    mesh_free(fe->mesh);
    free(fe);
}

// Initialize the id array and set nactive
int fem_assign_ids(fem_t fe)
{
    int numnp = fe->mesh->numnp;
    int ndof = fe->ndof;
    int* id = fe->id;
    int next_id = 0;
    for (int i = 0; i < numnp; ++i)
        for (int j = 0; j < ndof; ++j)
            if (id[j+i*ndof] >= 0)
                id[j+i*ndof] = next_id++;
    fe->nactive = next_id;
    return next_id;
}

// Decrement U by du_red
void fem_update_U(fem_t fe, double* du_red)
{
    double* U = fe->U;
    int* id   = fe->id;
    int ndof  = fe->ndof;
    int numnp = fe->mesh->numnp;
    for (int i = 0; i < numnp; ++i)
        for (int j = 0; j < ndof; ++j)
            if (id[j+i*ndof] >= 0)
                U[j+i*ndof] -= du_red[id[j+i*ndof]];
}

// Call the callback on each nodes (node position, force vector)
void fem_set_load(fem_t fe, void (*f)(double* x, double* fx))
{
    int d     = fe->mesh->d;
    int numnp = fe->mesh->numnp;
    int ndof  = fe->ndof;
    double* X = fe->mesh->X;
    double* F = fe->F;
    for (int i = 0; i < numnp; ++i)
        (*f)(X+i*d, F+i*ndof);
}

/**
 * ## Matrix assembly loop
 * 
 * The assembly loop logically executes `A[iglobal, jglobal] += Ae[i, j]`
 * for every local index pair `(i,j)`.  We filter out the contributions
 * where the global indices are negative (indicating that these
 * contributions are not needed because of an essential boundary condition.
 *
 *   The `ids` array implements the map $\iota$ from local
 *   indices to global indices (i.e. `ids[ilocal] = iglobal`).
 */
void assemble_matrix(matrix_t K, double* emat, int* ids, int ne)
{
    for (int je = 0; je < ne; ++je) {
        int j = ids[je];
        for (int ie = 0; ie <= je; ++ie) {
            int i = ids[ie];
            if (i >= 0 && j >= i)
	      matrix_add(K,i,j, densematn_get(emat,ne,ie,je));
        }
    }
}

/**
 * ## Vector assembly
 * 
 * We only really use one vector representation (a simple array), so
 * there is no need for the same type of matrix abstraction for vectors
 * that we have for matrices.  The semantics of `assemble_vector` are
 * similar to those of `assemble_matrix`, except now
 * we add the element vector `ve` into the global vector `v`.
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

/**
 * ## Whole-mesh  assembly
 */

// Assemble global residual and tangent stiffness (general)
void fem_assemble(fem_t fe, double* R, matrix_t K)
{
    int numelt       = fe->mesh->numelt;
    int nen          = fe->mesh->nen;
    element_t etype = fe->etype;

    // Set up local storage for element contributions
    int* ids   =     int_calloc(nen);
    double* Re = R ? double_calloc(nen) : NULL;
    double* Ke = K ? double_calloc(nen*nen) : NULL;

    // Clear storage for assembly
    if (R) double_clear(R, fe->nactive);
    if (K) matrix_clear(K);

    // Assemble contributions
    for (int i = 0; i < numelt; ++i) {

        // Get element contributions
        element_dR(etype, fe, i, Re, Ke);

        // Figure out where to put them
        int* elt = fe->mesh->elt + i*nen;
        for (int j = 0; j < nen; ++j)
            ids[j] = fe->id[elt[j]];

        // Put them into the global vector/matrix
        if (R) assemble_vector(R, Re, ids, nen);
        if (K) assemble_matrix(K, Ke, ids, nen);

    }

    // Free local storage
    if (Ke) free(Ke);
    if (Re) free(Re);
    free(ids);
}

// Convenience function for assembling band matrix
void fem_assemble_band(fem_t fe, double* R, bandmat_t K)
{
    if (K) {
        struct matrix_t Kmatrix;
        init_matrix_band(&Kmatrix, K);
        fem_assemble(fe, R, &Kmatrix);
    } else {
        fem_assemble(fe, R, NULL);
    }
}

// Convenience function for assembling dense matrix
void fem_assemble_dense(fem_t fe, double* R, densemat_t K)
{
    if (K) {
        struct matrix_t Kmatrix;
        init_matrix_dense(&Kmatrix, K);
        fem_assemble(fe, R, &Kmatrix);
    } else {
        fem_assemble(fe, R, NULL);
    }
}

// Print mesh state
void fem_print(fem_t fe)
{
    printf("\nNodal information:\n");
    printf("       ID ");
    for (int j = 0; j < fe->mesh->d; ++j) printf("     X%d", j);
    for (int j = 0; j < fe->ndof; ++j)   printf("     U%d", j);
    for (int j = 0; j < fe->ndof; ++j)   printf("     F%d", j);
    printf("\n");
    for (int i = 0; i < fe->mesh->numnp; ++i) {
        printf("%3d : % 3d ", i, fe->id[i]);
        for (int j = 0; j < fe->mesh->d; ++j)
            printf(" %6.2g", fe->mesh->X[j+fe->mesh->d*i]);
        for (int j = 0; j < fe->ndof; ++j)
            printf(" % 6.2g", fe->U[j+fe->ndof*i]);
        for (int j = 0; j < fe->ndof; ++j)
            printf(" % 6.2g", fe->F[j+fe->ndof*i]);
        printf("\n");
    }
    mesh_print_elt(fe->mesh);
}
