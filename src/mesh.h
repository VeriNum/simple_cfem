#ifndef MESH_H
#define MESH_H

//ldoc on
/**
 * # Mesh geometry
 * 
 * A mesh consists of an array of nodes locations $x_j \in \mathbb{R}^d$
 * and an element connectivity array with `elt[i,j]` giving the node
 * number for the $i$th node of the $j$th element.
 * 
 * We note that the ordering of the nodes within an element usually has
 * some significance.
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
    
} mesh_t;

mesh_t* malloc_mesh(int d, int numnp, int nen, int numelt);
void free_mesh(mesh_t* mesh);
mesh_t* mesh_create1d(int numelt, int degree, double a, double b);

void mesh_print_nodes(mesh_t* mesh);
void mesh_print_elt(mesh_t* mesh);
void mesh_print(mesh_t* mesh);

//ldoc off
#endif /* MESH_H */
