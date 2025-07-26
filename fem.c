#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
    return next_id;
}

void fem_get_elt_ids(fem_t* fe, int eltid, int* ids)
{
    int nen = fe->nen;
    int* elt = fe->elt + eltid*nen;
    for (int i = 0; i < nen; ++i)
        ids[i] = fe->id[elt[i]];
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
