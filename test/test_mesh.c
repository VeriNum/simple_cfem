#include <stdio.h>
#include <math.h>
#include <assert.h>

#include "mesh.h"

// Hand checked reference mesh for P1 quads

static double XrefP1[] = {
    0.0, 0.0,  1.0/3, 0.0,  2.0/3, 0.0,  1.0, 0.0,
    0.0, 0.5,  1.0/3, 0.5,  2.0/3, 0.5,  1.0, 0.5,    
    0.0, 1.0,  1.0/3, 1.0,  2.0/3, 1.0,  1.0, 1.0,    
};

static int erefP1[] = {
    0, 1, 5, 4,
    1, 2, 6, 5,
    2, 3, 7, 6,
    4, 5, 9, 8,
    5, 6, 10, 9,
    6, 7, 11, 10
};

// Hand checked reference mesh for P2 quads

static double XrefP2[] = {
    0.0/6, 0.0,  1.0/6, 0.0,  2.0/6, 0.0,  3.0/6, 0.0,
    4.0/6, 0.0,  5.0/6, 0.0,  1,     0.0,
    
    0.0/6, 0.25, 1.0/6, 0.25, 2.0/6, 0.25, 3.0/6, 0.25,
    4.0/6, 0.25, 5.0/6, 0.25, 1,     0.25,
    
    0.0/6, 0.5,  1.0/6, 0.5,  2.0/6, 0.5,  3.0/6, 0.5,
    4.0/6, 0.5,  5.0/6, 0.5,  1,     0.5,
    
    0.0/6, 0.75, 1.0/6, 0.75, 2.0/6, 0.75, 3.0/6, 0.75,
    4.0/6, 0.75, 5.0/6, 0.75, 1,     0.75,

    0.0/6, 1.0,  1.0/6, 1.0,  2.0/6, 1.0,  3.0/6, 1.0,
    4.0/6, 1.0,  5.0/6, 1.0,  1,     1.0};

static int erefP2[] = {
     0,   1,   2,   9,  16,  15,  14,   7,   8,
     2,   3,   4,  11,  18,  17,  16,   9,  10,
     4,   5,   6,  13,  20,  19,  18,  11,  12,
    14,  15,  16,  23,  30,  29,  28,  21,  22,
    16,  17,  18,  25,  32,  31,  30,  23,  24,
    18,  19,  20,  27,  34,  33,  32,  25,  26};

// Hand checked reference mesh for S2 quads

static double XrefS2[] = {
    0.0/6, 0.0,   1.0/6, 0.0,   2.0/6, 0.0,  3.0/6, 0.0,
    4.0/6, 0.0,   5.0/6, 0.0,   1.0,   0.0,

    0.0/3, 0.25,  1.0/3, 0.25,  2.0/3, 0.25, 1.0,   0.25,

    0.0/6, 0.5,   1.0/6, 0.5,   2.0/6, 0.5,  3.0/6, 0.5,
    4.0/6, 0.5,   5.0/6, 0.5,   1.0,   0.5,

    0.0/3, 0.75,  1.0/3, 0.75,  2.0/3, 0.75, 1.0,   0.75,
    
    0.0/6, 1.0,   1.0/6, 1.0,   2.0/6, 1.0,  3.0/6, 1.0,
    4.0/6, 1.0,   5.0/6, 1.0,   1.0,   1.0};

static int erefS2[] = {
     0,   1,   2,   8,  13,  12,  11,   7,
     2,   3,   4,   9,  15,  14,  13,   8,
     4,   5,   6,  10,  17,  16,  15,   9,
    11,  12,  13,  19,  24,  23,  22,  18,
    13,  14,  15,  20,  26,  25,  24,  19,
    15,  16,  17,  21,  28,  27,  26,  20};

// Hand checked reference mesh for triangles (nodes = P1 quad nodes)
static int erefT1[] = {};

void check_mesh(mesh_t* mesh, 
                int numnp, double* Xref,
                int numelt, int nen, int* eref)
{
    assert(mesh->nen == nen);
    assert(mesh->shape(NULL, NULL, Xref) == nen);
    assert(mesh->numnp == numnp);
    assert(mesh->numelt == numelt);

    for (int i = 0; i < 2*numnp; ++i)
        assert(fabs(Xref[i] - mesh->X[i]) < 1e-8);
    for (int i = 0; i < nen*numelt; ++i)
        assert(eref[i] == mesh->elt[i]);
}

int main()
{
    mesh_t* mesh = mesh_block2d_P1(3,2);
    check_mesh(mesh, 12, XrefP1, 6, 4, erefP1);
    free_mesh(mesh);

    mesh = mesh_block2d_P2(3,2);
    check_mesh(mesh, 35, XrefP2, 6, 9, erefP2);
    free_mesh(mesh);

    mesh = mesh_block2d_S2(3,2);
    check_mesh(mesh, 29, XrefS2, 6, 8, erefS2);
    free_mesh(mesh);
    
    mesh = mesh_block2d_T1(3,2);
//    check_mesh(mesh, 12, XrefP1, 12, 3, erefT1);
    mesh_print(mesh);
    free_mesh(mesh);
    
    return 0;
}
