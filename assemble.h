#ifndef ASSEMBLE_H
#define ASSEMBLE_H

// Interface for general assembler object (callback + context)
typedef struct assemble_t {
    void* p;                                // Context
    void (*add)(void*, double*, int*, int); // Add contribution
} assemble_t;

struct bandmat_t;

// Assembler setups
void init_assemble_band(assemble_t* assembler, struct bandmat_t* b);
void init_assemble_vector(assemble_t* assembler, double* v);

// Assembler methods
void assemble_add(assemble_t* assembler, double* emat, int* ids, int ne);

#endif /* ASSEMBLE_H */
