#ifndef GAUSSQUAD_H
#define GAUSSQUAD_H

//ldoc on
/**
 * # Gaussian-Legendre quadrature rules
 * 
 * Gauss-Legendre quadrature rules (sometimes just called Gauss
 * quadrature rules when the context is clear) approximate integrals
 * with formulas of the form
 * $$
 *   \int_{-1}^1 f(x) \, dx \approx
 *   \sum_{j=1}^p f(\xi_{jp}) w_{jp},
 * $$
 * where $\xi_{jp}$ and $w_{jp}$ are referred to as the quadrature
 * nodes (or points) and weights, respectively.  Gauss quadrature
 * rules are characterized by the fact that they are exact when $f$ is
 * a polynomial of degree at most $2p-1$.
 * 
 * Gauss-Legendre nodes are zeros of Legendre polynomials, while the
 * weights can be computed via an eigenvalue decomposition (using the
 * Golub-Welsch algorithm).  However, we do not need very high-order
 * quadrature rules, and so only provide nodes and weights for rules
 * up to $p = 10$, which are tabulated in many places.
 * 
 * Note that our code uses zero-based indexing (C-style) for indexing
 * the quadrature nodes, even though the expression we wrote above
 * uses the one-based indexing more common in presentations in the
 * numerical methods literature.
 * 
 */
double gauss_point(int i, int npts);
double gauss_weight(int i, int npts);

//ldoc off
#endif /* GAUSSQUAD_H */
