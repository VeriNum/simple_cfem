#include <stdlib.h>
#include <string.h>

#include "shapes1d.h"
#include "gaussquad.h"
#include "assemble.h"
#include "fem.h"
#include "element.h"

typedef struct poisson_elt_t {

    // Right hand side
    double (*f)(double x);

    // Scratch storage
    double Re[4];
    double Ke[4*4];

    // Scratch storage for quadrature point stuff
    double N[4];
    double dN[4];
    double x;
    double wt;

    // Dispatch object
    element_t e;

} poisson_elt_t;

static void set_qpoint1d(double* N, double* dN, double* xout, double* wtout,
                         fem_t* fe, int* elt, int k)
{
    int nen    = fe->nen;
    int degree = nen-1;

    // Get reference domain quantities
    double xi = gauss_point(k, degree);
    double wt = gauss_weight(k, degree);
    shapes1d(N, xi, degree);
    dshapes1d(dN, xi, degree);

    // Map xi to spatial domain (and derivative dx/dxi)
    double x = 0.0;
    double dx_dxi = 0.0;
    double* X = fe->X;
    for (int i = 0; i < nen; ++i) {
        int ni = elt[i];
        x += N[i]*X[ni];
        dx_dxi += dN[i]*X[ni];
    }

    // Transform gradients and quadrature weight
    for (int i = 0; i < nen; ++i)
        dN[i] /= dx_dxi;
    wt *= dx_dxi;

    // Set output parameters
    *xout = x;
    *wtout = wt;
}

static void poisson_elt_add(void* p, struct fem_t* fe, int eltid,
                            double* R, struct assemble_t* K)
{
    int nen = fe->nen;
    int degree = nen-1;
    int nquad = degree; // Would need one more for mass matrix...
    int* elt = fe->elt + eltid*nen;

    // Clear element storage
    poisson_elt_t* le = (poisson_elt_t*) p;
    double* Re = le->Re;
    double* Ke = le->Ke;
    if (R) memset(Re, 0, nen*sizeof(double));
    if (K) memset(Ke, 0, nen*nen*sizeof(double));

    for (int k = 0; k < nquad; ++k) {

        // Get information about quadrature point (spatial)
        double* N  = le->N;
        double* dN = le->dN;
        double x, wt;
        set_qpoint1d(N, dN, &x, &wt, fe, fe->elt + eltid*nen, k);

        // Add residual
        if (R) {
            double du = 0.0;
            double* U = fe->U;
            for (int j = 0; j < nen; ++j)
                du += dN[j]*U[elt[j]];
            for (int i = 0; i < nen; ++i) {
                double fx = le->f ? le->f(x) : 0.0;
                Re[i] += (dN[i]*du - N[i]*fx) * wt;
            }
        }

        // Add tangent stiffness
        if (K) {
            for (int j = 0; j < nen; ++j)
                for (int i = 0; i < nen; ++i)
                    Ke[i+j*nen] += dN[i]*dN[j] * wt;
        }
    }

    // Pass the local contribution to the assembler
    int ids[4];
    fem_get_elt_ids(fe, eltid, ids);
    if (R) assemble_vector(R, Re, ids, nen);
    if (K) assemble_add(K, Ke, ids, nen);
}

static void poisson_elt_free(void* p)
{
    free(p);
}

/*
 * Public interface
 */

element_t* malloc_poisson_element(double (*f)(double))
{
    poisson_elt_t* le = (poisson_elt_t*) malloc(sizeof(poisson_elt_t));
    le->f = f;
    le->e.p = le;
    le->e.add = poisson_elt_add;
    le->e.free = poisson_elt_free;
    return &(le->e);
}

void free_element(element_t* e)
{
    (*(e->free))(e->p);
}

void element_add(element_t* e, struct fem_t* fe, int eltid,
                 double* R, struct assemble_t* K)
{
    (*(e->add))(e->p, fe, eltid, R, K);
}
