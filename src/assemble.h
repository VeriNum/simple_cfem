#ifndef ASSEMBLE_H
#define ASSEMBLE_H

// Interface for general assembler object (callback + context)
typedef struct assemble_t {
    void* p;                                // Context
    void (*add)(void*, double*, int*, int); // Add contribution
    void (*clear)(void*);                   // Clear
} assemble_t;

// Assembler setups
void init_assemble_dense(assemble_t* assembler, double* A);
void init_assemble_band(assemble_t* assembler, double* b);

// Assembler methods
void assemble_add(assemble_t* assembler, double* emat, int* ids, int ne);
void assemble_clear(assemble_t* assembler);

// Direct vector assembly
void assemble_vector(double* v, double* ve, int* ids, int ne);

#endif /* ASSEMBLE_H */
