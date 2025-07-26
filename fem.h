#ifndef FEM1D_H
#define FEM1D_H

struct element_t;
struct assembler_t;

typedef struct fem_t {

    // Element type (NB: can generalize with multiple types)
    struct element_t* etype;

    // Mesh storage
    double* X;  // Node locations (d-by-numnp)
    double* U;  // Global array of solution values (ndof-by-numnp)
    double* F;  // Global array of forcing values (ndof-by-numnp)
    int* id;    // Global to reduced ID map (ndof-by-numnp)
    int* elt;   // Element connectivity array (nen-by-numelt)

    // Dimensions
    int d;       // Spatial dimension of problem (d = 1)
    int ndof;    // Number of unknowns per nodal point (ndof = 1)
    int numnp;   // Number of nodal points
    int numelt;  // Number of elements
    int nen;     // Number of element nodes
    int nactive; // Number of active dofs

} fem_t;

// Allocate/free an FEM problem structure
fem_t* malloc_fem(int numelt, int degree);
void free_fem(fem_t* fe);

// Initialize a regular mesh for an FEM problem
void fem_mesh(fem_t* fe, double a, double b);

// Assign dof IDs (and return the number of free dofs)
int fem_assign_ids(fem_t* fe);

// Update active part of U
void fem_update_U(fem_t* fe, double* ured);

// Assemble matrix and RHS
void fem_assemble(fem_t* fe, double* R, struct assemble_t* Kassembler);
void fem_assemble_band(fem_t* fe, double* R, double* K);

// Print the mesh
void fem_print(fem_t* fe);

#endif /* FEM1D_H */
