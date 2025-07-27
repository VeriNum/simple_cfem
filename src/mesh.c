#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "mesh.h"

void mesh_open(mesh_t* mesh, int d, int numnp, int nen, int numelt)
{
    mesh->d      = d;
    mesh->numnp  = numnp;
    mesh->nen    = nen;
    mesh->numelt = numelt;
    mesh->X      = malloc(d   * numnp  * sizeof(double));
    mesh->elt    = malloc(nen * numelt * sizeof(int));
}

void mesh_close(mesh_t* mesh)
{
    free(mesh->elt);
    free(mesh->X);
}

mesh_t* malloc_mesh(int d, int numnp, int nen, int numelt)
{
    mesh_t* mesh = malloc(sizeof(mesh_t));
    mesh->d      = d;
    mesh->numnp  = numnp;
    mesh->nen    = nen;
    mesh->numelt = numelt;
    mesh->X      = malloc(d   * numnp  * sizeof(double));
    mesh->elt    = malloc(nen * numelt * sizeof(int));
    return mesh;
}

void free_mesh(mesh_t* mesh)
{
    free(mesh->elt);
    free(mesh->X);
    free(mesh);
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
