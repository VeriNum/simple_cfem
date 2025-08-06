#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "assemble.h"
#include "element.h"
#include "bandmat.h"
#include "mesh.h"
#include "fem.h"

//ldoc on
/**
 * ## Implementation
 */
// Allocate mesh object
fem_t* fem_malloc(mesh_t* mesh, int ndof)
{
    int numnp = mesh->numnp;

    fem_t* fe = malloc(sizeof(fem_t));
    fe->mesh    = mesh;
    fe->etype   = NULL;
    fe->ndof    = ndof;
    fe->nactive = numnp * ndof;

    fe->U  = (double*) calloc(ndof * numnp, sizeof(double));
    fe->F  = (double*) calloc(ndof * numnp, sizeof(double));
    fe->id = (int*)    calloc(ndof * numnp, sizeof(int));

    return fe;
}

// Free mesh object
void fem_free(fem_t* fe)
{
    free(fe->id);
    free(fe->F);
    free(fe->U);
    mesh_free(fe->mesh);
    free(fe);
}

// Initialize the id array and set nactive
int fem_assign_ids(fem_t* fe)
{
    int numnp = fe->mesh->numnp;
    int* id = fe->id;
    int next_id = 0;
    for (int i = 0; i < numnp; ++i)
        if (id[i] >= 0)
            id[i] = next_id++;
    fe->nactive = next_id;
    return next_id;
}

// Decrement U by du_red
void fem_update_U(fem_t* fe, double* du_red)
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
void fem_set_load(fem_t* fe, void (*f)(double* x, double* fx))
{
    int d     = fe->mesh->d;
    int numnp = fe->mesh->numnp;
    int ndof  = fe->ndof;
    double* X = fe->mesh->X;
    double* F = fe->F;
    for (int i = 0; i < numnp; ++i)
        (*f)(X+i*d, F+i*ndof);
}

// Assemble global residual and tangent stiffness (general)
void fem_assemble(fem_t* fe, double* R, assemble_t* K)
{
    int numelt       = fe->mesh->numelt;
    int nen          = fe->mesh->nen;
    element_t* etype = fe->etype;

    // Set up local storage for element contributions
    int* ids   =     calloc(nen,     sizeof(int));
    double* Re = R ? calloc(nen,     sizeof(double)) : NULL;
    double* Ke = K ? calloc(nen*nen, sizeof(double)) : NULL;

    // Clear storage for assembly
    if (R) memset(R, 0, fe->nactive * sizeof(double));
    if (K) assemble_clear(K);

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
        if (K) assemble_add(K, Ke, ids, nen);

    }

    // Free local storage
    if (Ke) free(Ke);
    if (Re) free(Re);
    free(ids);
}

// Convenience function for assembling band matrix
void fem_assemble_band(fem_t* fe, double* R, bandmat_t* K)
{
    if (K) {
        assemble_t Kassembler;
        init_assemble_band(&Kassembler, K);
        fem_assemble(fe, R, &Kassembler);
    } else {
        fem_assemble(fe, R, NULL);
    }
}

// Convenience function for assembling dense matrix
void fem_assemble_dense(fem_t* fe, double* R, densemat_t* K)
{
    if (K) {
        assemble_t Kassembler;
        init_assemble_dense(&Kassembler, K);
        fem_assemble(fe, R, &Kassembler);
    } else {
        fem_assemble(fe, R, NULL);
    }
}

// Print mesh state
void fem_print(fem_t* fe)
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
