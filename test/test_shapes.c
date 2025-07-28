#include <math.h>
#include <assert.h>
#include <string.h>
#include <stdio.h>

#include "vecmat.h"
#include "shapes.h"

void test_shape(shapes_t shape, double* nodes, int d, int numnodes)
{
    double* N = malloc_vecmat(numnodes,1);
    for (int i = 0; i < numnodes; ++i) {
        shape(N, NULL, nodes+i*d);
        N[i] -= 1.0;
        assert(vecmat_norm(N) < 1e-8);
    }
    free_vecmat(N);
}


void test_dshape(shapes_t shape, double* x0, int d, int numnodes)
{
    double* Np = malloc_vecmat(numnodes,1);
    double* Nm = malloc_vecmat(numnodes,1);
    double* dN = malloc_vecmat(numnodes,d);
    double h = 1e-6;

    double xp[3], xm[3];
    shape(NULL, dN, x0);
    for (int j = 0; j < d; ++j) {
        memcpy(xp, x0, d*sizeof(double));
        memcpy(xm, x0, d*sizeof(double));
        xp[j] += h;  shape(Np, NULL, xp);
        xm[j] -= h;  shape(Nm, NULL, xm);
        for (int k = 0; k < numnodes; ++k) {
            double dN_kj_fd = (Np[k]-Nm[k])/2/h;
            assert(fabs(dN_kj_fd - dN[k+j*numnodes]) < 1e-8);
        }
    }

    free_vecmat(dN);
    free_vecmat(Nm);
    free_vecmat(Np);
}


static double nodes_1dP1[] = { -1.0, 1.0 };
static double nodes_1dP2[] = { -1.0, 0.0, 1.0 };
static double nodes_1dP3[] = { -1.0, -1.0/3, 1.0/3, 1.0 };
static double x1test[] = { 0.876 };

static double nodes_2dP1[] = {
    -1.0, -1.0,
     1.0, -1.0,
     1.0,  1.0,
    -1.0,  1.0};

static double nodes_2dP2[] = {
    -1.0, -1.0,
     0.0, -1.0,
     1.0, -1.0,
     1.0,  0.0,
     1.0,  1.0,
     0.0,  1.0,
    -1.0,  1.0,
    -1.0,  0.0,
     0.0,  0.0};

static double nodes_2dT1[] = {
    0.0, 0.0,
    1.0, 0.0,
    0.0, 1.0};

static double x2test[] = { 0.1312, 0.2488 };

int main()
{
    test_shape(shapes1dP1, nodes_1dP1, 1, 2);
    test_shape(shapes1dP2, nodes_1dP2, 1, 3);
    test_shape(shapes1dP3, nodes_1dP3, 1, 4);
    test_shape(shapes2dP1, nodes_2dP1, 2, 4);
    test_shape(shapes2dP2, nodes_2dP2, 2, 9);
    test_shape(shapes2dS2, nodes_2dP2, 2, 8);
    test_shape(shapes2dT1, nodes_2dT1, 2, 3);

    test_dshape(shapes1dP1, x1test, 1, 2);
    test_dshape(shapes1dP2, x1test, 1, 3);
    test_dshape(shapes1dP3, x1test, 1, 4);
    test_dshape(shapes2dP1, x2test, 2, 4);
    test_dshape(shapes2dP2, x2test, 2, 9);
    test_dshape(shapes2dS2, x2test, 2, 8);
    test_dshape(shapes2dT1, x2test, 2, 3);

    return 0;
}
