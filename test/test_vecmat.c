#include <string.h>
#include <assert.h>
#include <math.h>
#include <stdio.h>

#include "vecmat.h"

int main()
{
    int ipiv[3];
    double* x = malloc_vecmat(3, 1);

    // Check dimension setup
    assert(vecmat(x)->m == 3);
    assert(vecmat(x)->n == 1);
    assert(vecmat(x)->data == x);

    // Check clear functionality
    memset(x, 0xF, 3*sizeof(double));
    vecmat_clear(x);
    assert(vecmat_norm(x) == 0.0);

    // Check Cholesky factorization of a reference matrix
    double* A = malloc_vecmat(3, 3);
    A[0] = 1.0;  A[1] =  2.0;  A[2] =  3.0;
    A[3] = 2.0;  A[4] = 20.0;  A[5] = 26.0;
    A[6] = 3.0;  A[7] = 26.0;  A[8] = 70.0;
    vecmat_cfactor(A);
    assert(A[0] == 1.0 && A[3] == 2.0 && A[6] == 3.0
                       && A[4] == 4.0 && A[7] == 5.0
                                      && A[8] == 6.0);

    // Check Cholesky solve on a reference matrix
    x[0] = 20.0;  x[1] = 168.0;  x[2] = 364.0;
    vecmat_csolve(A, x);
    assert(x[0] == 2.0 && x[1] == 3.0 && x[2] == 4.0);

    // Check LU factorization of a reference matrix
    A[0] = 2.25; A[3] = 5.25; A[6] = 15.375;
    A[1] = 1.5;  A[4] = 8.0;  A[7] = 9.5;
    A[2] = 3.0;  A[5] = 4.0;  A[8] = 5.0;
    vecmat_lufactor(ipiv, A);
    assert(ipiv[0] == 2 && ipiv[1] == 1 && ipiv[2] == 2);
    assert(A[0] == 3.0  && A[3] == 4.0   && A[6] == 5.0 &&
           A[1] == 0.5  && A[4] == 6.0   && A[7] == 7.0 &&
           A[2] == 0.75 && A[5] == 0.375 && A[8] == 9.0);

    // Check LU solve on a reference matrix
    x[0] = 186.375; x[1] = 149.0; x[2] = 88.0;
    vecmat_lusolve(ipiv, A, x);
    assert(x[0] == 5.0 && x[1] == 7.0 && x[2] == 9.0);

    // Check LU transpose solve on reference matrix
    x[0] = 25.5; x[1] = 62.5; x[2] = 93.75;
    vecmat_lusolveT(ipiv, A, x);
    printf("%g %g %g\n", x[0], x[1], x[2]);
    assert(x[0] == 2.0 && x[1] == 4.0 && x[2] == 5.0);

    // Check norm
    x[0] = 3.0; x[1] = 4.0; x[2] = 0.0;
    assert(vecmat_norm2(x) == 5.0);

    free_vecmat(A);
    free_vecmat(x);
    return 0;
}
