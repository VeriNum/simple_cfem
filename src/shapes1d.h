#ifndef SHAPES1D_H
#define SHAPES1D_H

//ldoc on
/**
 * ## Shape functions
 * 

 * Our 1D shape functions are Lagrange polynomials for equally-spaced
 * nodes in the interval $[-1, 1]$; that is, if $x_0 = -1, \ldots
 * x_{p} = 1$ are $p+1$ equally-spaced nodes on the interval, then
 * $N_i$ is the unique polynomial of maximal degree $p$ such that
 * $N_i(x_j) = \delta_{ij}$.
 * 
 * We only implement shape function families up to order $p = 3$.
 * Shape functions with equally spaced nodes are only sensible for
 * modest values of $p$, as high-order polynomial interpolation
 * through equally-spaced points is poorly behaved.  When finite
 * element codes implement very high order elements, they usually use
 * a non-equispaced mesh (e.g. Gauss-Lobatto-Legendre nodes) that are
 * better behaved for interpolation.
 */

void shapes1d(double* N, double x, int degree);
void dshapes1d(double* dN, double x, int degree);

//ldoc off
#endif /* SHAPES1D_H */
