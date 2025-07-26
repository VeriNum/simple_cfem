#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#include "vecmat.h"

double* malloc_vecmat(int m, int n)
{
    vecmat_head_t* h = malloc(sizeof(vecmat_head_t) + (m*n-1)*sizeof(double));
    h->m = m;
    h->n = n;
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

void vecmat_clear(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    int m = vm->m, n = vm->n;
    double* A = vm->data;
    memset(A, 0, m*n * sizeof(double));
}

void vecmat_print(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    int m = vm->m, n = vm->n;
    double* A = vm->data;
    printf("%d-by-%d\n", m, n);
    for (int i = 0; i < m; ++i) {
        for (int j = 0; j < n; ++j)
            printf(" % 6.2g", A[i+j*m]);
        printf("\n");
    }
}

double vecmat_norm2(double* data)
{
    vecmat_head_t* vm = vecmat(data);
    int m = vm->m, n = vm->n;
    double* A = vm->data;
    double result = 0.0;
    for (int j = 0; j < n; ++j)
        for (int i = 0; i < m; ++i) {
            double Aij = A[i+j*m];
            result += Aij*Aij;
        }
    return sqrt(result);
}

double vecmat_norm(double* data)
{
    return sqrt(vecmat_norm2(data));
}
