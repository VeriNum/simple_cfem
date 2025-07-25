#ifndef ASSEMBLE_H
#define ASSEMBLE_H


// Interface for general assembler callback
typedef void (*assemble_fun_t)(void*, double*, int*, int);

// Interface for general assembler object (callback + context)
typedef struct {
    void* p;           // Assembler context object
    assemble_fun_t f;  // Assembler function
} assemble_t;

void assemble_add(assemble_t* assembler, double*, int*, int);


typedef struct {
    double* P;  // Column-major n-by-b storage (for b diagonals)
    int n, b;
} band_assembler_t;

// Assemble into a band matrix
void add_to_band(void* p, double* emat, int* ids, int ne);


// Assemble into a vector
void add_to_vector(void* p, double* evec, int* ids, int ne);


#endif /* ASSEMBLE_H */
