#include <stdlib.h>
#include <string.h>

#include "shapes.h"
#include "quadrules.h"
#include "assemble.h"
#include "mesh.h"
#include "fem.h"
#include "element.h"

//ldoc on
/**
 * ## Method dispatch
 * 
 * As usual for when we do OOP in C, we have dispatch functions
 * that essentially trampoline a call to the appropriate function
 * pointer in an element object's dispatch table.
 */
// Call element dR method
void element_dR(element_t* e, struct fem_t* fe, int eltid,
                double* Re, double* Ke)
{
    (*(e->dR))(e->p, fe, eltid, Re, Ke);
}

// Call element free
void free_element(element_t* e)
{
    (*(e->free))(e->p);
}

/**
 * We write our Poisson interface to illustrate the general pattern,
 * even though we could in principle simplify it (because we are not
 * carrying around any element parameters in this case).  The internal
 * wiring is:
 * 
 * - Element type data is stored in a structure like `poisson1d_elt_t`.
 * - One field of the specific element is an `element_t` containing
 *   the methods table for the element.
 * - The data pointer in the `element_t` field points back to the
 *   containing struct (the `poisson1d_elt_t` in this case).
 * 
 * Externally, we always pass around `element_t` pointers.  Internally,
 * we always use the more specific `poisson1d_elt_t` from the `element_t`
 * data pointer.
 */
// Poisson element type data structure
typedef struct poisson1d_elt_t {
    // Material parameters, etc go here in more complex cases
    element_t e; // For dispatch table
} poisson1d_elt_t;

// Declare methods for Poisson element type
static void poisson1d_elt_dR(void* p, fem_t* fe, int eltid,
                           double* Re, double* Ke);
static void poisson1d_elt_free(void* p);

// Allocate a Poisson element type
element_t* malloc_poisson1d_element()
{
    poisson1d_elt_t* le = (poisson1d_elt_t*) malloc(sizeof(poisson1d_elt_t));
    le->e.p = le;
    le->e.dR = poisson1d_elt_dR;
    le->e.free = poisson1d_elt_free;
    return &(le->e);
}

// Free a Poisson element type
static void poisson1d_elt_free(void* p)
{
    free(p);
}

/**
 * ## 1D Poisson element
 * 
 * The 1D Poisson element `dR` routine computes the local residual terms
 * $$
 *  R^e(u, N^e_i(x)) = 
 *  \int_{\Omega_e} 
 *  \left( \nabla N^e_i(x) \cdot \nabla u(x) - N^e_i(x) f(x) \right) \,
 *  d\Omega(x).
 * $$
 * The functions $u(x)$ is represented on $\Omega_e$ in terms of
 * the element shape functions
 * $$
 *   u(x) = \sum_i N^e_i(x) u_i
 * $$
 * and similarly for $f(x)$.  The tangent matrix has entries
 * $$
 *  \partial ( R^e(u(x), N^e_i(x)) )/\partial u_j =
 *  \int_{\Omega_e} \nabla N^e_i(x) \cdot \nabla N^e_j(x) \, d\Omega(x).
 * $$
 * We organize the computation of the integrals (both for the residual
 * vector and the tangent matrix) as an outer loop over quadrature nodes
 * and inner loops over the shape function indices at the quadrature node.
 * 
 * We compute integrals using *mapped* quadrature: the locations of quadrature
 * points in element reference domains are mapped to the element spatial
 * domain, and the weights are multiplied by the Jacobian determinant for this
 * computation.
 */
static void poisson1d_elt_dR(
    void* p,                   // Context pointer (not used)
    fem_t* fe, int eltid,      // Mesh and element ID in mesh
    double* Re, double* Ke)    // Outputs: element residual and tangent
{
    int nen  = fe->mesh->nen;
    int ndof = fe->ndof;
    int degree = nen-1;
    int nquad = degree; // Would need one more for mass matrix...
    int* elt = fe->mesh->elt + eltid*nen;

    // Clear element storage
    if (Re) memset(Re, 0, nen*sizeof(double));
    if (Ke) memset(Ke, 0, nen*nen*sizeof(double));

    for (int k = 0; k < nquad; ++k) {

        // Get information about quadrature point (spatial)
        double N[4];  // Storage for shape functions
        double dN[4]; // Storage for shape derivatives
        double x  = gauss_point(k, nquad);
        double wt = gauss_weight(k, nquad);
        mesh_shapes(fe->mesh, eltid, &x, N, dN);

        // Add residual
        if (Re) {
            double du = 0.0;
            double fx = 0.0;
            double* U = fe->U;
            double* F = fe->F;
            for (int j = 0; j < nen; ++j) {
                du += dN[j]*U[ndof*elt[j]];
                fx += N[j]*F[ndof*elt[j]];
            }
            for (int i = 0; i < nen; ++i)
                Re[i] += (dN[i]*du - N[i]*fx) * wt;
        }

        // Add tangent stiffness
        if (Ke) {
            for (int j = 0; j < nen; ++j)
                for (int i = 0; i < nen; ++i)
                    Ke[i+j*nen] += dN[i]*dN[j] * wt;
        }
    }
}
