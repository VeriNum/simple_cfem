#ifndef ELEMENT_H
#define ELEMENT_H

struct fem_t;

//ldoc on
/**
 * # Elements
 * 
 * Abstractly, for steady-state problems, we are finding 
 * $u(x) = \sum_j N_j(x) u_j$ via an equation
 * $$
 *   R(u, N_i) = 0
 * $$
 * for all shape functions $N_i$ that are not associated with
 * essential boundary conditions.  The element routines compute
 * the contribution of one element to the residual $R$ and to 
 * the tangent $\partial R/\partial u_j$.
 * 
 * Different types of equations demand different types of elements.
 * Even for a single type of element, we may depend on things like
 * PDE coefficients or choices of material parameters (as well as
 * implementation details like the quadrature rule used for computing
 * integrals).  An `element_t` object type keeps all this information
 * together.  The `element_t` data type should be thought of as
 * representing a *type* of element, and not one specific element;
 * usually many elements share fundamentally the same data, differing
 * only in which nodes they involve.  In the language of design patterns,
 * this is an example of a "flyweight" pattern.
 * 
 * The main interface for an element is a method
 * 
 *     dR(p, fe, eltid, Re, Ke)
 * 
 * where `p` is context data for the element type, `fe` is a finite
 * element mesh data structure, `eltid` is the index of the element in
 * the mesh, and `Re` and `Ke` are pointers to storage for the element
 * residual and tangent matrix contributions.  Either `Re` or `Ke` can
 * be null, indicating that we don't need that output.
 * 
 * We also provide a destructor method (`free`) for releasing
 * resources used by the `element_t` instance.
 * 
 */
// Element type interface
typedef struct element_t {
    void *p; // Context pointer
    void (*dR)(void* p, struct fem_t* fe, int eltid,
              double* Re, double* Ke);
    void (*free)(void* p);
} *element_t;

// Wrappers for calling the dR and free method
void element_dR(element_t e, struct fem_t* fe, int eltid,
                double* Re, double* Ke);
void element_free(element_t e);

/**
 * Write now, we only have one element type, corresponding to a 1D Poisson
 * problem, written in weak form as
 * $$
 *  R(u, N_i) =
 *  \int_{\Omega} \left(
 *  \nabla N_i(x) \cdot \nabla u(x) -
 *  N_i(x) f(x) \right) \, d\Omega(x).
 * $$
 * There are no PDE coefficients or other special parameters to keep 
 * track of for this element tyle.
 */
element_t malloc_poisson1d_element(void);
element_t malloc_poisson2d_element(void);

//ldoc off
#endif /* ELEMENT_H */
