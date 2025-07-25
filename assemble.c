#include <stdio.h>
#include <assert.h>

#include "assemble.h"

void add_to_band(void* p, double* emat, int* ids, int ne)
{
    band_assembler_t* assembler = (band_assembler_t*) p;
    double* P = assembler->P;
    int n = assembler->n;
    int b = assembler->b;

    for (int je = 0; je < ne; ++je) {
        int j = ids[je];
        for (int ie = 0; ie <= je; ++ie) {
            int i = ids[ie];
            int d = j-i;
            if (j >= 0 && d >= 0) {
                assert(d <= b);
                P[j+n*d] += emat[ie+ne*je];
            }
        }
    }
}

void add_to_vec(void* p, double* evec, int* ids, int ne)
{
    double* vec = (double*) p;
    for (int ie = 0; ie < ne; ++ie) {
        int i = ids[ie];
        if (i >= 0)
            vec[i] += evec[ie];
    }
}
