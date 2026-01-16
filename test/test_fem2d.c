#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>

#include <densemat.h>
#include <bandmat.h>
#include "mesh.h"
#include "matrix.h"
#include "element.h"
#include "fem.h"


// Set up the mesh on [0,1]^2 with Dirichlet BC
void test_fem1(void)
{
    mesh_t mesh = mesh_block2d_P1(2, 2);
    fem_t fe = fem_malloc(mesh, 1);
    fe->etype = malloc_poisson2d_element();

    // Move midpoint to off center (patch test!)
    fe->mesh->X[2*4+0] = 0.6;
    fe->mesh->X[2*4+1] = 0.4;

    // BC at x = 0
    fe->id[0] = -1;  fe->U[0] = 0.0;
    fe->id[3] = -1;  fe->U[3] = 0.0;
    fe->id[6] = -1;  fe->U[6] = 0.0;

    // BC at x = 1;
    fe->id[2] = -1;  fe->U[2] = 1.0;
    fe->id[5] = -1;  fe->U[5] = 1.0;
    fe->id[8] = -1;  fe->U[8] = 1.0;

    fem_assign_ids(fe);

    // Set up globals and assemble system
    densemat_t R = densemat_malloc(fe->nactive, 1);
    densemat_t K = densemat_malloc(fe->nactive, fe->nactive);
    fem_assemble_dense(fe, R->data, K);

    // Factor, solve, and update
    densemat_cfactor(K);
    densemat_csolve(K, R->data);
    fem_update_U(fe, R->data);

    // Check against reference solution (u = x)
    for (int i = 0; i < fe->mesh->numnp; ++i) {
        assert(fabs(fe->mesh->X[2*i] - fe->U[i]) < 1e-8);
    }

    densemat_free(K);
    densemat_free(R);
    element_free(fe->etype);
    fem_free(fe);
}

int main(void)
{
    test_fem1();
    return 0;
}
