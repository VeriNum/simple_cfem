#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "vecmat.h"
#include "mesh.h"

//ldoc on
/**
 * ## Memory management
 */
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

/**
 * ## Meshes in 1D
 * 
 * The simplest mesher creates a 1D mesh on an interval
 * $[a,b]$. Elements are ordered from left to right.  We allow
 * elements of order 1-3.
 */
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

/**
 * ## Quad meshes in 2D
 * 
 * All the 2D quad meshers produce meshes of `nex` by `ney` elements,
 * ordered in row-major order starting in the southwest and proceeding
 * to the northeast.  The nodes are listed going counterclockwise around
 * the element (except possibly the last node in the P2 case).
 * 
 * We start with the P1 case, which is the simplest (only corner nodes).
 */
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

/**
 * For P2 elements, each element involves three consecutive rows and
 * columns of the logical array of nodes.  This at least remains
 * mostly straightforward.
 */
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

/**
 * The serendipity element block mesher is a little more complicated
 * than P1 or P2, because we don't have a regular grid of mesh points
 * (because we don't need mesh points in the middle of our elements.
 */
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

/**
 * ## 2D triangular meshes
 * 
 * The 2D linear triangle mesher is like the P1 mesher, but each quad
 * is comprised of two triangles with a common edge going from the
 * southeast to the northwest edge of the quad.
 */
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

/**
 * ## Reference to spatial mapping
 */
void mesh_to_spatial(mesh_t* mesh, int eltid, double* xref,
                     double* x, int* ipiv, double* J,
                     double* N, double* dN)
{
    int d = mesh->d;
    int* elt = mesh->elt + mesh->nen * eltid;
    double* X = mesh->X;

    // Get shape function
    int nshape = (*mesh->shape)(N, dN, xref);

    // Build x if requested
    if (x && N) {
        memset(x, 0, d * sizeof(double));
        for (int k = 0; k < nshape; ++k)
            for (int i = 0; i < d; ++i)
                x[i] += X[i+d*elt[k]] * N[k];
    }

    // Build and factor J and transform dN if requested
    if (ipiv && J && dN) {

        // Form J
        memset(J, 0, d * d * sizeof(double));
        for (int k = 0; k < nshape; ++k)
            for (int j = 0; j < d; ++j)
                for (int i = 0; i < d; ++i)
                    J[i+j*d] += X[i+d*elt[k]] * dN[k+j*nshape];

        // Factor
        dense_vecmatn_lufactor(ipiv, J, d);

        // Transform shape derivatives to spatial coordinates
        for (int k = 0; k < nshape; ++k) {
            double dNk[3];
            for (int j = 0; j < d; ++j)
                dNk[j] = dN[k+j*nshape];
            dense_vecmatn_lusolveT(ipiv, J, dNk, d);
            for (int j = 0; j < d; ++j)
                dN[k+j*nshape] = dNk[j];
        }
    }
}

double mesh_shapes(mesh_t* mesh, int eltid, double* x,
                   double* N, double* dN)
{
    // Allocate space to make a 3D element work
    int ipiv[3];
    double J[9];
    double xout[3];
    int d = mesh->d;

    // Call mesh_to_spatial
    mesh_to_spatial(mesh, eltid, x, xout, ipiv, J, N, dN);
    memcpy(x, xout, d * sizeof(double));

    // If we asked for J, return the Jacobian
    return dN ? dense_vecmatn_lujac(ipiv, J, d) : 0.0;
}

/**
 * ## I/O routines
 */
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
