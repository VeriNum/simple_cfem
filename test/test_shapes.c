#include <math.h>
#include <assert.h>
#include <string.h>
#include <stdio.h>

#include "../src/densemat.h"
#include "../src/shapes.h"

void test_shape(shapes_t shape, double* nodes, int d, int numnodes)
{
    densemat_t* N = densemat_malloc(numnodes,1);
    for (int i = 0; i < numnodes; ++i) {
        shape(N->data, NULL, nodes+i*d);
        N->data[i] -= 1.0;
        assert(densemat_norm(N) < 1e-8);
    }
    densemat_free(N);
}


void test_dshape(shapes_t shape, double* x0, int d, int numnodes)
{
    densemat_t* Np = densemat_malloc(numnodes,1);
    densemat_t* Nm = densemat_malloc(numnodes,1);
    densemat_t* dN = densemat_malloc(numnodes,d);
    double h = 1e-6;

    double xp[3], xm[3];
    shape(NULL, dN->data, x0);
    for (int j = 0; j < d; ++j) {
        memcpy(xp, x0, d*sizeof(double));
        memcpy(xm, x0, d*sizeof(double));
        xp[j] += h;  shape(Np->data, NULL, xp);
        xm[j] -= h;  shape(Nm->data, NULL, xm);
        for (int k = 0; k < numnodes; ++k) {
            double dN_kj_fd = (Np->data[k]-Nm->data[k])/2/h;
            assert(fabs(dN_kj_fd - dN->data[k+j*numnodes]) < 1e-8);
        }
    }

    densemat_free(dN);
    densemat_free(Nm);
    densemat_free(Np);
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

int main(void)
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
