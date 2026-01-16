#ifndef FEM1D_H
#define FEM1D_H
#include "mesh.h"
#include "matrix.h"
struct element_t;

//ldoc on
/**
 * # Finite element mesh
 * 
 * My finite element mesh data structure is informed by lots of
 * old Fortran codes, and mostly is a big pile of arrays.
 * Specifically, we have the nodal arrays:
 * 
 * - `U`: Global array of solution values, *including* those that
 *   are determined by Dirichlet boundary conditions.  Column
 *   $j$ represents the unknowns at node $j$ in the mesh.
 * - `F`: Global array of load values (right hand side evaluations
 *   of the forcing function in Poisson, for example; but 
 *   Neumann boundary conditions can also contribute to `F`).
 * - `id`: Indices of solution values in a reduced solution vector.
 *   One column per node, with the same dimensions as `U` (and `F`),
 *   so that `ureduced[id[i,j]]` corresponds to `U[i,j]` when
 *   `id[i,j]` is nonnegative.  The reduced solution vector contains only
 *   those variables that are not constrained a priori by boundary
 *   conditions; we mark the latter with negative entries in the `id`
 *   array.
 * 
 * We also keep around a pointer to a mesh and an element type object.
 * Note that for the moment, we are assuming only one element type
 * per problem -- we could have a separate array of element type pointer
 * (one per element) if we wanted more flexibility.
 * 
 */
typedef struct fem_t {

    // Mesh data
    struct mesh_t *mesh;

    // Element type (NB: can generalize with multiple types)
    struct element_t *etype;

    // Storage for fields
    double* U;  // Global array of solution values (ndof-by-numnp)
    double* F;  // Global array of forcing values (ndof-by-numnp)
    int* id;    // Global to reduced ID map (ndof-by-numnp)

    // Dimensions
    int ndof;    // Number of unknowns per nodal point (tested only with ndof = 1)
    int nactive; // Number of active dofs

} *fem_t;

/**
 * ## Mesh operations
 */
fem_t fem_malloc(mesh_t mesh, int ndof);
void fem_free(fem_t fe);

/**
 * The `fem_assign_ids` function sets up the `id` array.  On input,
 * the `id` array in the mesh structure should be initialized so that
 * boundary values are marked with negative numbers (and everything else
 * non-negative).  On output, entries of the `id` array for variables not
 * subject to essential boundary conditions will be assigned indices from
 * 0 to `nactive` (and `nactive` will be updated appropriately).
 */
int fem_assign_ids(fem_t fe);

/**
 * The `fem_update_U` function applies an update to the internal state.
 * By update, we mean that `U[i,j] -= du_red[id[i,j]]` for `id[i,j] > 0`.
 * 
 * If the update comes from $K^{-1} R$ where $K$ is the reduced tangent
 * and $R$ is the reduced residual, then  applying the update will
 * exactly solve the equation in the linear case.  However, we can also
 * apply approximate updates (e.g. with an inexact solver for $K$),
 * and the same framework works for Newton iterations for nonlinear problems.
 * 
 */
void fem_update_U(fem_t fe, double* du_red);

/**
 * The `fem_set_load` function iterates through all nodes in the mesh,
 * and for each node calls a callback function.  The arguments to the
 * callback are the node position (an input argument) and the node
 * loading / right-hand side vector (an output argument).
 */
void fem_set_load(fem_t fe, void (*f)(double* x, double* fx));

/**
 * The following two functions need not be public except for unit tests;
 * normally they're called only from fem_assemble.
 */
void assemble_matrix(matrix_t K, double* emat, int* ids, int ne);
void assemble_vector(double* v, double* ve, int* ids, int ne);


/**
 * # Assembly
 * 
 * Each element in a finite element discretization consists of
 * 
 * - A domain $\Omega_e$ for the $e$th element, and
 * - Local shape functions $N^e_1, \ldots, N^e_m$, which are often
 *   Lagrange functions for interpolation at some set of nodes
 *   in $\Omega_e$.
 * 
 * Each local shape function on the domain $\Omega_e$ is the
 * restriction of some global shape function on the whole
 * domain $\Omega$.  That is, we have global shape functions
 * $$
 *   N_{j}(x) = \sum_{j = \iota(j',e)} N^e_{j'}(x),
 * $$
 * where $\iota(j,e)$ denotes the mapping from the local shape
 * function index for element $e$ to the corresponding global shape
 * function index.  We only ever compute explicitly with the local
 * functions $N^e_j$; the global functions are implicit.
 * 
 * *Assembly* is the process of reconstructing a quantity defined in
 * terms of global shape functions from the contributions of the
 * individual elements and their local shape functions.  For example,
 * to compute
 * $$
 *   F_i = \int_{\Omega} f(x) N_i(x) \, dx,
 * $$
 * we rewrite the integral as
 * $$
 *   F_i = \sum_{i = \iota(i',e)} \int_{\Omega_e} f(x) N^e_{i'}(x) \, dx.
 * $$
 * In code, this is separated into two pieces:
 * 
 * - Compute element contributions $\int_{\Omega_e} f(x) N^e_{i'}(x) \, dx$.
 *   This is the responsibility of the element implementation.
 * - Sum contributions into the global position $i$ corresponding to
 *   the element-local index $i'$.  This is managed by an assembly loop.
 * 
 * The concept of an "assembly loop" is central to finite element methods,
 * but it is not unique to this setting.  For example, circuit simulators
 * similarly construct system matrices (conductance, capacitance, etc)
 * via the contributions of circuit elements (resistors, capacitors,
 * inductors, and so forth).
 * 
 * We have two types of assembly loops that we care about: those that
 * involve pairs of shape functions and result in matrices, and
 * those that explicitly involve only a single shape function and result
 * in vectors.
 * 
 * We will sometimes also want to discard some element contributions
 * that correspond to interactions with shape functions associated with
 * known boundary values (for example).  We also handle this filtering
 * work as part of our assembly process.
 * 
 * The assembly loops iterate through the elements and produce a global
 * residual and tangent stiffness based on the current solution state.
 * The residual and tangent matrix assembler are passed in by pointers;
 * a `NULL` pointer means "do not assemble this".
 */
void fem_assemble(fem_t fe, double* R, matrix_t Kmatrix);
void fem_assemble_band(fem_t fe, double* R, bandmat_t K);
void fem_assemble_dense(fem_t fe, double* R, densemat_t K);

/**
 * For debugging small problems, it is also useful to have a routine to
 * print out all the mesh arrays.
 */
void fem_print(fem_t fe);

//ldoc off
#endif /* FEM1D_H */
