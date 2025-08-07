#include <string.h>
#include <assert.h>
#include <math.h>
#include <stdio.h>

#include "densemat.h"

int main(void)
{
    int ipiv[3];
    densemat_t x = densemat_malloc(3, 1);

    // Check dimension setup
    assert(x->m == 3);
    assert(x->n == 1);

    // Check clear functionality
    memset(x->data, 0xF, 3*sizeof(double));
    densemat_clear(x);
    assert(densemat_norm(x) == 0.0);

    // Check Cholesky factorization of a reference matrix
    densemat_t A = densemat_malloc(3, 3);
    A->data[0] = 1.0;  A->data[1] =  2.0;  A->data[2] =  3.0;
    A->data[3] = 2.0;  A->data[4] = 20.0;  A->data[5] = 26.0;
    A->data[6] = 3.0;  A->data[7] = 26.0;  A->data[8] = 70.0;
    densemat_cfactor(A);
    assert(A->data[0] == 1.0 && A->data[3] == 2.0 && A->data[6] == 3.0
                       && A->data[4] == 4.0 && A->data[7] == 5.0
                                      && A->data[8] == 6.0);

    // Check Cholesky solve on a reference matrix
    x->data[0] = 20.0;  x->data[1] = 168.0;  x->data[2] = 364.0;
    densemat_csolve(A, x->data);
    assert(x->data[0] == 2.0 && x->data[1] == 3.0 && x->data[2] == 4.0);

    // Check LU factorization of a reference matrix
    A->data[0] = 2.25; A->data[3] = 5.25; A->data[6] = 15.375;
    A->data[1] = 1.5;  A->data[4] = 8.0;  A->data[7] = 9.5;
    A->data[2] = 3.0;  A->data[5] = 4.0;  A->data[8] = 5.0;
    densemat_lufactor(ipiv, A);
    assert(ipiv[0] == 2 && ipiv[1] == 1 && ipiv[2] == 2);
    assert(A->data[0] == 3.0  && A->data[3] == 4.0   && A->data[6] == 5.0 &&
           A->data[1] == 0.5  && A->data[4] == 6.0   && A->data[7] == 7.0 &&
           A->data[2] == 0.75 && A->data[5] == 0.375 && A->data[8] == 9.0);

    // Check Jacobian determinant
    assert(densemat_lujac(ipiv, A) == -162.0);

    // Check LU solve on a reference matrix
    x->data[0] = 186.375; x->data[1] = 149.0; x->data[2] = 88.0;
    densemat_lusolve(ipiv, A, x->data);
    assert(x->data[0] == 5.0 && x->data[1] == 7.0 && x->data[2] == 9.0);

    // Check LU transpose solve on reference matrix
    x->data[0] = 25.5; x->data[1] = 62.5; x->data[2] = 93.75;
    densemat_lusolveT(ipiv, A, x->data);
    assert(x->data[0] == 2.0 && x->data[1] == 4.0 && x->data[2] == 5.0);

    // Check norm
    x->data[0] = 3.0; x->data[1] = 4.0; x->data[2] = 0.0;
    assert(densemat_norm(x) == 5.0);

    densemat_free(A);
    densemat_free(x);
    return 0;
}
