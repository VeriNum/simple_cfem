#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "assemble.h"
#include "element.h"
#include "bandmat.h"
#include "fem.h"


fem_t* malloc_fem(int numelt, int degree)
{
    fem_t* fe = malloc(sizeof(fem_t));
    int d = 1;
    int ndof = 1;
    int numnp = numelt * degree + 1;
    int nen = degree + 1;

    fe->etype = NULL;
    fe->d = d;
    fe->ndof = ndof;
    fe->numnp = numnp;
    fe->numelt = numelt;
    fe->nen = nen;
    fe->nactive = numnp * ndof;

    fe->X   = (double*) malloc(d    * numnp  * sizeof(double));
    fe->U   = (double*) malloc(ndof * numnp  * sizeof(double));
    fe->F   = (double*) malloc(ndof * numnp  * sizeof(double));
    fe->id  = (int*)    malloc(ndof * numnp  * sizeof(int));
    fe->elt = (int*)    malloc(nen  * numelt * sizeof(int));

    return fe;
}

void free_fem(fem_t* fe)
{
    free(fe->elt);
    free(fe->id);
    free(fe->F);
    free(fe->U);
    free(fe->X);
    free(fe);
}

void fem_mesh(fem_t* fe, double a, double b)
{
    int numnp = fe->numnp;
    int numelt = fe->numelt;
    int nen = fe->nen;

    // Set up equispaced mesh of points
    for (int i = 0; i < numnp; ++i)
        fe->X[i] = (i*b + (numnp-i-1)*a)/(numnp-1);

    // Set up element connectivity
    for (int j = 0; j < numelt; ++j)
        for (int i = 0; i < nen; ++i)
            fe->elt[i+j*nen] = i+j*(nen-1);

    // Clear the other arrays
    memset(fe->U,  0, numnp * sizeof(double));
    memset(fe->F,  0, numnp * sizeof(double));
    memset(fe->id, 0, numnp * sizeof(int));
}

int fem_assign_ids(fem_t* fe)
{
    int numnp = fe->numnp;
    int* id = fe->id;
    int next_id = 0;
    for (int i = 0; i < numnp; ++i)
        if (id[i] >= 0)
            id[i] = next_id++;
    fe->nactive = next_id;
    return next_id;
}

void fem_update_U(fem_t* fe, double* ured)
{
    double* U = fe->U;
    int* id = fe->id;
    int numnp = fe->numnp;
    for (int i = 0; i < numnp; ++i)
        if (id[i] >= 0)
            U[i] -= ured[id[i]];
}

void fem_assemble(fem_t* fe, double* R, assemble_t* K)
{
    int numelt = fe->numelt;
    element_t* etype = fe->etype;
    int nen = fe->nen;

    // Set up local storage for element contributions
    int* ids = (int*) malloc(nen * sizeof(int));
    double* Re = R ? malloc(nen * sizeof(double)) : NULL;
    double* Ke = K ? malloc(nen * nen * sizeof(double)) : NULL;

    // Clear storage for assembly
    if (R) memset(R, 0, fe->nactive * sizeof(double));
    if (K) assemble_clear(K);

    // Assemble contributions
    for (int i = 0; i < numelt; ++i) {

        // Get element contributions
        element_dR(etype, fe, i, Re, Ke);

        // Figure out where to put them
        int* elt = fe->elt + i*nen;
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

void fem_print(fem_t* fe)
{
    printf("\nNodal information:\n");
    printf("   : ID :      X      U      F\n");
    for (int i = 0; i < fe->numnp; ++i) {
        printf("%3d: % 3d: % 6.2g % 6.2g % 6.2g\n",
               i, fe->id[i], fe->X[i], fe->U[i], fe->F[i]);
    }

    printf("\nElement connectivity:\n");
    for (int i = 0; i < fe->numelt; ++i) {
        printf("% 3d:", i);
        for (int j = 0; j < fe->nen; ++j)
            printf("  % 3d", fe->elt[j + i*(fe->nen)]);
        printf("\n");
    }
}
