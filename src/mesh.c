#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mesh.h"

mesh_t* malloc_mesh(int d, int numnp, int nen, int numelt)
{
    mesh_t* mesh = malloc(sizeof(mesh_t));
    mesh->d      = d;
    mesh->numnp  = numnp;
    mesh->nen    = nen;
    mesh->numelt = numelt;
    mesh->X      = calloc(d   * numnp,  sizeof(double));
    mesh->elt    = calloc(nen * numelt, sizeof(int));
    return mesh;
}

void free_mesh(mesh_t* mesh)
{
    free(mesh->elt);
    free(mesh->X);
    free(mesh);
}

mesh_t* mesh_create1d(int numelt, int degree, double a, double b)
{
    int numnp = numelt * degree + 1;
    int nen = degree + 1;
    mesh_t* mesh = malloc_mesh(1, numnp, nen, numelt);

    // Set up equispaced mesh of points
    double* X = mesh->X;
    for (int i = 0; i < numnp; ++i)
        X[i] = (i*b + (numnp-i-1)*a)/(numnp-1);

    // Set up element connectivity
    int* elt = mesh->elt;
    for (int j = 0; j < numelt; ++j)
        for (int i = 0; i < nen; ++i)
            elt[i+j*nen] = i+j*(nen-1);

    return mesh;
}

void mesh_print_nodes(mesh_t* mesh)
{
    printf("\nNodal positions:\n");
    printf("   ID ");
    for (int j = 0; j < mesh->d; ++j)
        printf("     X%d", j);
    printf("\n");
    for (int i = 0; i < mesh->numnp; ++i) {
        printf("%3d : ", i);
        double* Xi = mesh->X + mesh->d*i;
        for (int j = 0; j < mesh->d; ++j)
            printf(" %6.2g", Xi[j]);
        printf("\n");
    }
}

void mesh_print_elt(mesh_t* mesh)
{
    printf("\nElement connectivity:\n");
    for (int i = 0; i < mesh->numelt; ++i) {
        printf("% 3d :", i);
        for (int j = 0; j < mesh->nen; ++j)
            printf("  % 3d", mesh->elt[j + i*(mesh->nen)]);
        printf("\n");
    }
}

void mesh_print(mesh_t* mesh)
{
    mesh_print_nodes(mesh);
    mesh_print_elt(mesh);
}
