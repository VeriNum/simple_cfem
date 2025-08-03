#ifndef GAUSSQUAD_H
#define GAUSSQUAD_H

//ldoc on
/**
 * # Quadrature rules
 * 
 * Quadrature rules approximate integrals with formulas of the form
 * $$
 *   \int_{\Omega} f(x) \, d\Omega(x) \approx
 *   \sum_{j=1}^p f(\xi_{j}) w_j
 * $$
 * where $\xi_j \in \Omega$ and $w_j \in \mathbb{R}$ are known as the
 * quadrature nodes (or points) and weights, respectively.
 * 
 * A good source of quadrature rules for various domains can be found in
 * Stroud's book on _Approximate calculation of multiple integrals_
 * (Prentice Hall, 1971).
 * 
 * ## Gaussian-Legendre quadrature rules
 * 
 * Gauss-Legendre quadrature rules (sometimes just called Gauss
 * quadrature rules when the context is clear) are $p$-point rules on
 * $[-1, 1]$ that are characterized by the fact that they are exact
 * when $f$ is a polynomial of degree at most $2p-1$.
 * 
 * Gauss-Legendre nodes are zeros of Legendre polynomials, while the
 * weights can be computed via an eigenvalue decomposition (using the
 * Golub-Welsch algorithm).  However, we do not need very high-order
 * quadrature rules, and so only provide nodes and weights for rules
 * up to $p = 10$ (probably more than we need), which are tabulated in
 * many places.  Because this is just a table lookup, we don't bother to
 * include the code in the automated documentation.
 * 
 * Note that our code uses zero-based indexing (C-style) for indexing
 * the quadrature nodes, even though the expression we wrote above
 * uses the one-based indexing more common in presentations in the
 * numerical methods literature.
 * 
 */
double gauss_point(int i, int npts);
double gauss_weight(int i, int npts);

/**
 * ## Product Gauss rules
 * 
 * A 2D tensor product Gauss rule for the domain $[-1,1]^2$ involves a
 * grid of quadrature points with coordinates given by 1D Gauss quadrature
 * rules.  We support rules with 1, 4, 9, or 16 points.
 */
void gauss2d_point(double* xi, int i, int npts);
double gauss2d_weight(int i, int npts);

/**
 * ## Mid-side rule
 * 
 * For a triangle, a rule based on the three mid-side values is exact
 * for every polynomial with total degree less than or equal to 2
 * (which is enough for our purposes).  This is sometimes called the
 * Hughes formula.
 */
void hughes_point(double* xi, int i, int npts);
double hughes_weight(int i, int npts);

//ldoc off
#endif /* GAUSSQUAD_H */
