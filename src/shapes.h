#ifndef SHAPES1D_H
#define SHAPES1D_H

//ldoc on
/**
 * # Shape functions
 * 
 * A *shape function* on a reference domain is a basis function used
 * for interpolation on that domain.  We will generally use Lagrange
 * shape functions (also called nodal shape functions), which are one
 * at one nodal point in a reference domain and zero at the others.
 * We want to be able to compute both the values of all shape functions
 * at a point in the domain and also their derivatives (stored as
 * a matrix with $d$ columns for a $d$-dimensional reference domain).
 * Our shape function implementations all have the following interface,
 * where the output arguments `N` and `dN` are used to store the
 * shape function values and derivative values.  If a `NULL` is given
 * for either of these output arguments, we just skip that part of the
 * computation.
 * 
 * The function returns the number of shape functions it computes.
 */
typedef int (*shapes_t)(double*, double*, double*);

/**
 * Our 1D shape functions are Lagrange polynomials for equally-spaced
 * nodes in the interval $[-1, 1]$.  We only go up to cubic
 * polynomials ($p = 3)$, as high-order polynomial interpolation
 * through equally-spaced points is poorly behaved.  When finite
 * element codes implement very high order elements, they usually use
 * a non-equispaced mesh (e.g. Gauss-Lobatto-Legendre nodes) that are
 * better behaved for interpolation.
 */
int shapes1dP1(double* N, double* dN, double* x);
int shapes1dP2(double* N, double* dN, double* x);
int shapes1dP3(double* N, double* dN, double* x);

/**
 * The 2D P1 and P2 shape functions are tensor products of 1D P1
 * and P2 elements.  The nodes are ordered counterclockwise, starting
 * with the bottom left corner of the square.  Thus, the P1 element
 * has the reference domain $[-1,1]^2$ and nodal points at the corners:
 * 
 *     3 -- 2
 *     |    |
 *     0 -- 1
 * 
 * while for the P2 element, we include the mid-side nodes and one node
 * in the middle (listed last):
 * 
 *     6 -- 5 -- 4
 *     |         |
 *     7    8    3
 *     |         |
 *     0 -- 1 -- 2
 * 
 * The S2 element (part of the "serendipity family") is identical to the P2
 * element except that it does not include the final node in the middle.
 */
int shapes2dP1(double* N, double* dN, double* x);
int shapes2dP2(double* N, double* dN, double* x);
int shapes2dS2(double* N, double* dN, double* x);

/**
 * Finally, we define shape functions for a triangle with the reference
 * domain with corners at $(0,0)$, $(0,1)$, and $(1,0)$, listed in that order.
 * 
 *     2
 *     | \
 *     0--1
 */
int shapes2dT1(double* N, double* dN, double* x);

//ldoc off
#endif /* SHAPES1D_H */
