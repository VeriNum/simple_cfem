#ifndef ASSEMBLE_H
#define ASSEMBLE_H

typedef struct {
    double* P;  // Column-major n-by-b storage (for b diagonals)
    int n, b;
} band_assembler_t;

// Interface for general assembler callback
typedef void (*assemble_fun_t)(void*, double*, int*, int);

// Assemble a matrix into a band
void add_to_band(void* p, double* emat, int* ids, int ne);

#endif /* ASSEMBLE_H */
