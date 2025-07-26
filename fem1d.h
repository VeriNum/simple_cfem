#ifndef FEM1D_H
#define FEM1D_H

typedef struct fem1d_t {

    // Mesh storage
    double* X;  // Node locations (d-by-numnp)
    double* U;  // Global array of solution values (ndof-by-numnp)
    double* F;  // Global array of forcing values (ndof-by-numnp)
    int* id;    // Global to reduced ID map (ndof-by-numnp)
    int* elt;   // Element connectivity array (nen-by-numelt)

    // Dimensions
    int d;      // Spatial dimension of problem (d = 1)
    int ndof;   // Number of unknowns per nodal point (ndof = 1)
    int numnp;  // Number of nodal points
    int numelt; // Number of elements
    int nen;    // Number of element nodes

} fem1d_t;

// Allocate/free an FEM problem structure
fem1d_t* malloc_fem1d(int numelt, int degree);
void free_fem1d(fem1d_t* fe);

// Initialize a regular mesh for an FEM problem
void fem1d_mesh(fem1d_t* fe, double a, double b);

// Assign dof IDs (and return the number of free dofs)
int fem1d_assign_ids(fem1d_t* fe);

// Print the mesh
void fem1d_print(fem1d_t* fe);

#endif /* FEM1D_H */
