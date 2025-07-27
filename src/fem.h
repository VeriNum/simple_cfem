#ifndef FEM1D_H
#define FEM1D_H

struct element_t;
struct assembler_t;
struct mesh_t;

//ldoc on
/**
 * # Finite element mesh
 * 
 * My finite element mesh data structure is informed by lots of
 * old Fortran codes, and mostly is a big pile of arrays.
 * Specifically, we have the nodal arrays:
 * 
 * - `X`: The node position arrays.  Column $j$ represents
 *   the coordinates of node $j$ in the mesh.
 * - `U`: Global array of solution values, *including* those that
 *   are determined by Dirichlet boundary conditions.  Column
 *   $j$ represents the unknowns at node $j$ in the mesh.
 * - `F`: Global array of load values (right hand side evaluations
 *   of the forcing function in Poisson, for example; but 
 *   Neumann boundary conditions can also contribute to `F`).
 * - `id`: Indices of solution values in a reduced solution vector.
 *   One column per node, with the same dimensions as `U` (and `F`),
 *   so that `ureduced[id[i,j]]` corresponds to `U[i,j]` when
 *   `id[i,j]` is positive.  The reduced solution vector contains only
 *   those variables that are not constrained a priori by boundary
 *   conditions; we mark the latter with negative entries in the `id`
 *   array.
 * 
 * In addition, we have the element connectivity array `elt`;
 * `elt[i,j]` gives the node number for the $i$th node of the $j$th
 * element.  We note that the ordering of the nodes within an element
 * usually has some significance in order to ensure positive orientation
 * of the mapping from reference to spatial coordinates (see the section
 * on mapped quadrature for details).
 * 
 * We also keep around a pointer to an element type object.
 * Note that for the moment, we are assuming only one element type
 * per problem -- we could have a separate array of element type pointer
 * (one per element) if we wanted more flexibility.
 * 
 */
typedef struct fem_t {

    // Mesh data
    struct mesh_t* mesh;

    // Element type (NB: can generalize with multiple types)
    struct element_t* etype;

    // Storage for fields
    double* U;  // Global array of solution values (ndof-by-numnp)
    double* F;  // Global array of forcing values (ndof-by-numnp)
    int* id;    // Global to reduced ID map (ndof-by-numnp)

    // Dimensions
    int ndof;    // Number of unknowns per nodal point (ndof = 1)
    int nactive; // Number of active dofs

} fem_t;

/**
 * ## Mesh operations
 */
fem_t* malloc_fem(struct mesh_t* mesh, int ndof);
void free_fem(fem_t* fe);

/**
 * The `fem_assign_ids` function sets up the `id` array.  On input,
 * the `id` array in the mesh structure should be initialized so that
 * boundary values are marked with negative numbers (and everything else
 * non-negative).  On output, entries of the `id` array for variables not
 * subject to essential boundary conditions will be assigned indices from
 * 0 to `nactive` (and `nactive` will be updated appropriately).
 */
int fem_assign_ids(fem_t* fe);

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
void fem_update_U(fem_t* fe, double* du_red);

/**
 * The `fem_set_load` function iterates through all nodes in the mesh,
 * and for each node calls a callback function.  The arguments to the
 * callback are the node position (an input argument) and the node
 * loading / right-hand side vector (an output argument).
 */
void fem_set_load(fem_t* fe, void (*f)(double* x, double* fx));

/**
 * The assembly loops iterate through the elements and produce a global
 * residual and tangent stiffness based on the current solution state.
 * The residual and tangent matrix assembler are passed in by pointers;
 * a `NULL` pointer means "do not assemble this".
 */
void fem_assemble(fem_t* fe, double* R, struct assemble_t* Kassembler);
void fem_assemble_band(fem_t* fe, double* R, double* K);
void fem_assemble_dense(fem_t* fe, double* R, double* K);

/**
 * For debugging small problems, it is also useful to have a routine to
 * print out all the mesh arrays.
 */
void fem_print(fem_t* fe);

//ldoc off
#endif /* FEM1D_H */
