#include <string.h>
#include <assert.h>
#include <math.h>
#include <stdio.h>

#include "vecmat.h"

int main()
{
    double* x = malloc_vecmat(3, 1);

    // Check dimension setup
    assert(vecmat(x)->m == 3);
    assert(vecmat(x)->n == 1);
    assert(vecmat(x)->data == x);

    // Check clear functionality
    memset(x, 0xF, 3*sizeof(double));
    vecmat_clear(x);
    assert(vecmat_norm(x) == 0.0);

    // Check factorization of a reference matrix
    double* A = malloc_vecmat(3, 3);
    A[0] = 1.0;  A[1] =  2.0;  A[2] =  3.0;
    A[3] = 2.0;  A[4] = 20.0;  A[5] = 26.0;
    A[6] = 3.0;  A[7] = 26.0;  A[8] = 70.0;
    vecmat_cfactor(A);
    assert(A[0] == 1.0 && A[3] == 2.0 && A[6] == 3.0
                       && A[4] == 4.0 && A[7] == 5.0
                                      && A[8] == 6.0);

    // Check solve on a reference matrix
    x[0] = 20.0;  x[1] = 168.0;  x[2] = 364.0;
    vecmat_csolve(A, x);
    assert(x[0] == 2.0 && x[1] == 3.0 && x[2] == 4.0);

    // Check norm
    x[0] = 3.0; x[1] = 4.0; x[2] = 0.0;
    assert(vecmat_norm2(x) == 5.0);

    free_vecmat(A);
    free_vecmat(x);
    return 0;
}
