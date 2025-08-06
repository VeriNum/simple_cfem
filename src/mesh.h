#ifndef MESH_H
#define MESH_H

#include "shapes.h"

//ldoc on
/**
 * # Mesh geometry
 * 
 * A mesh consists of an array of nodes locations $x_j \in
 * \mathbb{R}^d$ and an element connectivity array with `elt[i,j]`
 * giving the node number for the $i$th node of the $j$th element.
 * 
 * Each element represents a subset of $\Omega_e \subset \mathbb{R}^d$
 * that is the image of a reference domain $\Omega_0 \subset
 * \mathbb{R}^d$ under a mapping
 * $$
 *   \chi(\xi) = \sum_{i=1}^{m} N^e_i(\xi) x_i
 * $$
 * where $x_1, \ldots, x_m$ are the $m$ element node positions.  The
 * functions $N^e_i$ are nodal basis functions (or Lagrange basis
 * functions, or cardinal functions) for an interpolation set $\xi_1,
 * \ldots, \xi_m \in \Omega_0$; that is $N_i(\xi_j) = \delta_{ij}$.
 * The reference domain nodes $\xi_i$ are typically placed at corners
 * or on edges of the reference domain, and their images are at
 * corresponding locations in $\Omega_e$.
 * 
 * When the same set of nodal basis functions (also called nodal shape
 * functions in a finite element setting) are used both for defining
 * the geometry and for approximating a PDE solution on $\Omega$, we
 * call this method of describing the geometry an *isoparametric* map.
 * 
 * We generally want our mappings describing the geometry to be
 * *positively oriented*: that is, the map $\chi$ should be invertible
 * and have positive Jacobian determinant over all of $\Omega_0$.
 * This puts some restrictions on the spatial positions of the nodes;
 * for example, if the interpolation nodes appear in counterclockwise
 * order in the reference domain $\Omega_0$, then the corresponding
 * spatial nodes in $\Omega_e$ should also appear in counterclockwise.
 * order.
 */
typedef struct mesh_t {

    // Mesh storage
    double* X;  // Node locations (d-by-numnp)
    int* elt;   // Element connectivity array (nen-by-numelt)

    // Dimensions
    int d;       // Spatial dimension of problem
    int numnp;   // Number of nodal points
    int nen;     // Number of element nodes
    int numelt;  // Number of elements

    // Shape function
    int (*shape)(double* N, double* dN, double* x);

} mesh_t;

/**
 * One *can* allocate objects and then work out the node positions and
 * element connectivity by hand (or with an external program).  But in
 * many cases, a simpler option is to programatically generate a mesh
 * that covers a simple domain (e.g. a block) and then map the
 * locations of the nodes.  One can construct more complex meshes by
 * combining this with a "tie" operation that merges the identity of
 * nodes in the same location, but we will not bother with tied meshes
 * for now.
 */
mesh_t* mesh_malloc(int d, int numnp, int nen, int numelt);
void mesh_free(mesh_t* mesh);

/**
 * The simplest mesher creates a 1D mesh on an interval $[a,b]$.
 * We allow elements of order 1-3.
 */
mesh_t* mesh_create1d(int numelt, int degree, double a, double b);

/**
 * Things are more complicated in 2D, and we have distinct mesh
 * generation routines for the different types of shape functions
 * described in the `shapes` module.  Each of these generates a mesh
 * of the region $[0,1]^2$ with `nex`-by-`ney` elements.
 */
mesh_t* mesh_block2d_P1(int nex, int ney);
mesh_t* mesh_block2d_P2(int nex, int ney);
mesh_t* mesh_block2d_S2(int nex, int ney);
mesh_t* mesh_block2d_T1(int nex, int ney);

/**
 * Given a mesh and a point in a reference geometry (given by an
 * element identifier `eltid` and coordinates `xref` in the element's
 * reference domain), we would like to be able to compute spatial
 * quantities (the shape functions, their spatial derivatives, and the
 * Jacobian of the reference to spatial map).  The Jacobian matrix
 * is in LU-factored form.
 */
void mesh_to_spatial(mesh_t* mesh, int eltid, double* xref,
                     double* x, int* ipiv, double* J,
                     double* N, double* dN);

/**
 * We frequently are interested just in the mapped point location,
 * shape functions and mapped derivatives, and the Jacobian
 * determinant.  So we provide a convenience wrapper around
 * `mesh_to_spatial` for this case.
 */
double mesh_shapes(mesh_t* mesh, int eltid, double* x,
                   double* N, double* dN);

/**
 * For debugging, it is helpful to be able to print out all or part of
 * the mesh geometry.
 */
void mesh_print_nodes(mesh_t* mesh);
void mesh_print_elt(mesh_t* mesh);
void mesh_print(mesh_t* mesh);

//ldoc off
#endif /* MESH_H */
