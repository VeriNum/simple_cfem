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
 * - Element type data is stored in a structure like `poisson_elt_t`.
 * - One field of the specific element is an `element_t` containing
 *   the methods table for the element.
 * - The data pointer in the `element_t` field points back to the
 *   containing struct (the `poisson_elt_t` in this case).
 * 
 * Externally, we always pass around `element_t` pointers.  Internally,
 * we always use the more specific `poisson_elt_t` from the `element_t`
 * data pointer.
 */
// Poisson element type data structure
typedef struct poisson_elt_t {
    // Material parameters, etc go here in more complex cases
    element_t e; // For dispatch table
} poisson_elt_t;

// Declare methods for Poisson element type
static void poisson_elt_dR(void* p, fem_t* fe, int eltid,
                           double* Re, double* Ke);
static void poisson_elt_free(void* p);

// Allocate a Poisson element type
element_t* malloc_poisson_element()
{
    poisson_elt_t* le = (poisson_elt_t*) malloc(sizeof(poisson_elt_t));
    le->e.p = le;
    le->e.dR = poisson_elt_dR;
    le->e.free = poisson_elt_free;
    return &(le->e);
}

// Free a Poisson element type
static void poisson_elt_free(void* p)
{
    free(p);
}

/**
 * ## Mapped quadrature
 * 
 * We previously defined quadrature rules and element shape functions
 * on a reference domain $[-1, 1]$; but our element subdomains are not all
 * simple copies of this reference domain!  Hence, we need a recipe for
 * converting our rule on a reference domain with coordinates $\xi$ into
 * a rule on an element domain in real space with coordinates $x$.
 * 
 * A *mapped* quadrature rule uses a coordinate mapping 
 * $x = \chi(\xi)$ to convert integrals over the element domain to
 * integrals over the reference domain.  A standard choice for
 * $\chi$ in the case of nodal shape functions is the *isoparametric map*
 * that interpolates the nodal coordinates using the shape functions:
 * $$
 *   \chi(\xi) = \sum_{i=1}^m N^e_i(\xi) x_i
 * $$
 * where $x_i$ is the location of node $i$.  We can also compute
 * the Jacobian matrix (1-by-1 for 1D problems)
 * $$
 *  J(\xi) = \chi'(\xi) = \sum_{i=1}^m (N^e_i)'(\xi).
 * $$
 * 
 * The change of variables formula for integration allows us to map
 * integrals in our real element domain back to reference domain:
 * $$
 *  \int_{\Omega_e} f(x) \, dx =
 *  \int_{\Omega_0} f(x(\xi)) 
 *   \det\left( \frac{\partial \chi}{\partial \xi} \right) \, d\xi.
 * $$
 * Applying a quadrature rule with nodes $\xi_i$ and weights $w_i$
 * to the reference domain integral, we have
 * $$
 *  \int_{\Omega_e} f(x) \, dx \approx
 *  \sum_j f(x(\xi_j)) \, \tilde{w}_j
 * $$
 * where $\tilde{w}_j = \det(J(\xi_j))$ with $J(\xi)$ denoting the
 * Jacobian $\partial \xi/\partial \xi$.  Note that we assume that the
 * Jacobian determinant of the mapping is positive.
 * 
 * Our weak forms generally involve derivatives of shape functions in $x$,
 * but we so far only have the derivatives of the shape functions with
 * respect to $\xi$.  Converting derivatives in reference coordinates to
 * spatial derivatives again involves the Jacobian determinant:
 * $$
 *   \frac{\partial N_i}{\partial x} =
 *   \frac{\partial N_i}{\partial \xi} J(\xi)^{-1}.
 * $$
 * We note a (standard) abuse of notation here: the symbol $N_i$ on
 * the left hand side equation is technically the reference shape function
 * $N_i$ composed with the inverse coordinate mapping $\chi^{-1}$.
 * 
 * Putting this all together, we want a function that at each quadrature
 * node $\xi_k$ will
 * 
 * - Compute shape functions and derivatives in the reference domain
 * - Use the isoparametric map to compute $x_k = \chi(\xi_k)$ 
 *   and $J_k = \chi'(\xi_k)$.
 * - Use $J_k$ to transform to spatial derivatives of the shape functions.
 * - Use $J_k$ to compute the mapped quadrature weight.
 * 
 * The following local function does all these steps (in 1D).
 * 
 */
static void set_qpoint1d(
    double* N,     // Shape functions at kth point
    double* dN,    // dN/dx at kth point
    double* xout,  // Location x of kth point
    double* wtout, // Quadrature weight (with Jacobian)
    fem_t* fe,     // Finite element mesh structure
    int* elt,      // Connectivity for current element
    int k)         // Index of quadrature point
{
    int d      = fe->mesh->d;
    int nen    = fe->mesh->nen;
    int degree = nen-1;

    // Get reference domain quantities
    double xi = gauss_point(k, degree);
    double wt = gauss_weight(k, degree);
    (*fe->mesh->shape)(N, dN, &xi);

    // Map xi to spatial domain (and derivative dx/dxi)
    double x = 0.0;
    double dx_dxi = 0.0;
    double* X = fe->mesh->X;
    for (int i = 0; i < nen; ++i) {
        int ni = elt[i];
        x += N[i]*X[ni*d];
        dx_dxi += dN[i]*X[ni*d];
    }

    // Transform gradients and quadrature weight
    for (int i = 0; i < nen; ++i)
        dN[i] /= dx_dxi;
    wt *= dx_dxi;

    // Set output parameters
    *xout = x;
    *wtout = wt;
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
 */
static void poisson_elt_dR(
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
        double x, wt;
        set_qpoint1d(N, dN, &x, &wt, fe, fe->mesh->elt + eltid*nen, k);

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
