#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

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
    mesh->shape  = NULL;
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

    if      (degree == 1) mesh->shape = shapes1dP1;
    else if (degree == 2) mesh->shape = shapes1dP2;
    else if (degree == 3) mesh->shape = shapes1dP3;
    else assert(0);

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

mesh_t* mesh_block2d_P1(int nex, int ney)
{
    int nx = nex+1, ny = ney+1;
    mesh_t* mesh = malloc_mesh(2, nx*ny, 4, nex*ney);
    mesh->shape = shapes2dP1;

    // Set up nodes (row-by-row, SW to NE)
    for (int iy = 0; iy < ney+1; ++iy)
        for (int ix = 0; ix < nex+1; ++ix) {
            int i = ix + iy*(nex+1);
            mesh->X[2*i+0] = ((double) ix)/(nx-1);
            mesh->X[2*i+1] = ((double) iy)/(ny-1);
        }

    // Set up element connectivity
    for (int iy = 0; iy < ney; ++iy)
        for (int ix = 0; ix < nex; ++ix) {
            int i = ix + iy*nex;
            int i_sw = ix + iy*(nex+1);
            mesh->elt[4*i+0] = i_sw;
            mesh->elt[4*i+1] = i_sw + 1;
            mesh->elt[4*i+2] = i_sw + 1 + nex+1;
            mesh->elt[4*i+3] = i_sw + nex+1;
        }

    return mesh;
}

mesh_t* mesh_block2d_P2(int nex, int ney)
{
    int nx = 2*nex+1, ny = 2*ney+1;
    mesh_t* mesh = malloc_mesh(2, nx*ny, 9, nex*ney);
    mesh->shape = shapes2dP2;

    // Set up nodes (row-by-row, SW to NE)
    for (int iy = 0; iy < ny; ++iy)
        for (int ix = 0; ix < nx; ++ix) {
            int i = ix + iy*nx;
            mesh->X[2*i+0] = ((double) ix)/(nx-1);
            mesh->X[2*i+1] = ((double) iy)/(ny-1);
        }

    // Set up element connectivity
    for (int iy = 0; iy < ney; ++iy)
        for (int ix = 0; ix < nex; ++ix) {
            int i = ix + iy*nex;
            int i_sw = (2*ix) + (2*iy)*nx;
            mesh->elt[9*i+0] = i_sw;
            mesh->elt[9*i+1] = i_sw + 1;
            mesh->elt[9*i+2] = i_sw + 2;
            mesh->elt[9*i+3] = i_sw + 2 + nx;
            mesh->elt[9*i+4] = i_sw + 2 + 2*nx;
            mesh->elt[9*i+5] = i_sw + 1 + 2*nx;
            mesh->elt[9*i+6] = i_sw +   + 2*nx;
            mesh->elt[9*i+7] = i_sw +   + nx;
            mesh->elt[9*i+8] = i_sw + 1 + nx;
        }

    return mesh;
}

mesh_t* mesh_block2d_S2(int nex, int ney)
{
    int nx0 = 2*nex+1, nx1 = nex+1; // Even/odd row sizes
    int numnp = (ney+1)*nx0 + ney*nx1;
    mesh_t* mesh = malloc_mesh(2, numnp, 8, nex*ney);
    mesh->shape = shapes2dS2;

    // Set up nodes (row-by-row, SW to NE)
    for (int iy = 0; iy < ney; ++iy) { // Element row index
        int start = iy*(nx0+nx1);

        // Fill bottom row
        for (int ix = 0; ix < nx0; ++ix) {
            mesh->X[2*(start+ix)+0] = ((double) ix)/(nx0-1);
            mesh->X[2*(start+ix)+1] = ((double) iy)/ney;
        }

        // Fill middle row
        start += nx0;
        for (int ix = 0; ix < nx1; ++ix) {
            mesh->X[2*(start+ix)+0] = ((double) ix)/(nx1-1);
            mesh->X[2*(start+ix)+1] = ((double) iy+0.5)/ney;
        }

        // Fill top row (may get overwritten by the same values shortly
        start += nx1;
        for (int ix = 0; ix < nx0; ++ix) {
            mesh->X[2*(start+ix)+0] = ((double) ix)/(nx0-1);
            mesh->X[2*(start+ix)+1] = ((double) iy+1.0)/ney;
        }
    }

    // Set up element connectivity
    for (int iy = 0; iy < ney; ++iy)
        for (int ix = 0; ix < nex; ++ix) {
            int i = ix + iy*nex;
            int i_sw = 2*ix + iy*(nx0+nx1);
            int i_ww =   ix + iy*(nx0+nx1) + nx0;
            int i_nw = 2*ix + iy*(nx0+nx1) + nx0+nx1;
            mesh->elt[8*i+0] = i_sw;
            mesh->elt[8*i+1] = i_sw + 1;
            mesh->elt[8*i+2] = i_sw + 2;
            mesh->elt[8*i+3] = i_ww + 1;
            mesh->elt[8*i+4] = i_nw + 2;
            mesh->elt[8*i+5] = i_nw + 1;
            mesh->elt[8*i+6] = i_nw;
            mesh->elt[8*i+7] = i_ww;
        }

    return mesh;
}

mesh_t* mesh_block2d_T1(int nex, int ney)
{
    int nx = nex+1, ny = ney+1;
    mesh_t* mesh = malloc_mesh(2, nx*ny, 3, 2*nex*ney);
    mesh->shape = shapes2dT1;

    // Set up nodes (row-by-row, SW to NE)
    for (int iy = 0; iy < ney+1; ++iy)
        for (int ix = 0; ix < nex+1; ++ix) {
            int i = ix + iy*(nex+1);
            mesh->X[2*i+0] = ((double) ix)/(nx-1);
            mesh->X[2*i+1] = ((double) iy)/(ny-1);
        }

    // Set up element connectivity
    for (int iy = 0; iy < ney; ++iy)
        for (int ix = 0; ix < nex; ++ix) {
            int i = ix + iy*nex;
            int i_sw = ix + iy*(nex+1);

            // Two triangles makes a square
            mesh->elt[6*i+0] = i_sw;
            mesh->elt[6*i+1] = i_sw + 1;
            mesh->elt[6*i+2] = i_sw + nex+1;
            mesh->elt[6*i+3] = i_sw + nex+1;
            mesh->elt[6*i+4] = i_sw + 1;
            mesh->elt[6*i+5] = i_sw + 1 + nex+1;
        }

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
