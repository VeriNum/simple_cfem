#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "vecmat.h"

double* malloc_vecmat(int m, int n)
{
    vecmat_head_t* h = malloc(sizeof(vecmat_head_t) + (m*n-1)*sizeof(double));
    return h->data;
}

void free_vecmat(double* data)
{
    free(vecmat(data));
}

vecmat_head_t* vecmat(double* data)
{
    vecmat_head_t dummy;
    void* p = (void*) data + ((void*) &dummy - (void*) dummy.data);
    return (vecmat_head_t*) p;
}

void vecmat_print(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    int m = vm->m, n = vm->n;
    double* A = vm->data;
    for (int i = 0; i < m; ++i) {
        for (int j = 0; j < n; ++j)
            printf(" % 6.2g", A[i+j*n]);
        printf("\n");
    }
}

void vecmat_clear(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    int m = vm->m, n = vm->n;
    double* A = vm->data;
    memset(A, 0, m*n * sizeof(double));
}
