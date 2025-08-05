#include <string.h>
#include <assert.h>
#include <math.h>
#include <stdio.h>

#include "vecmat.h"
#include "bandmat.h"

void get_Aref(double* A)
{
    static double Aref[] = {
        // Randomly generated matrix (6-by-6)...
        5.611573028354077,
        0.4567405138512043,
        1.5563566615211313,
        0.0,
        0.0,
        0.0,
        0.4567405138512043,
        4.757747564652157,
        1.395776410174324,
        0.31352657528440375,
        0.0,
        0.0,
        1.5563566615211313,
        1.395776410174324,
        5.689183174271518,
        1.0184064385847038,
        1.0560604548088794,
        0.0,
        0.0,
        0.31352657528440375,
        1.0184064385847038,
        5.703049575775514,
        1.509589258389374,
        1.83183662372477,
        0.0,
        0.0,
        1.0560604548088794,
        1.509589258389374,
        5.7857136854295845,
        0.8755526167936731,
        0.0,
        0.0,
        0.0,
        1.83183662372477,
        0.8755526167936731,
        4.25791871147544
    };
    memcpy(A, Aref, 36*sizeof(double));
}

void get_bref(double* b)
{
    static double bref[] = {
        // Randomly generated vector (len 6)...
        0.9176326489491068,
        0.8622794808080309,
        0.59767235440732,
        0.5456893881835098,
        0.4788475407133893,
        0.597614144120541
    };
    memcpy(b, bref, 6*sizeof(double));
}

void get_xref(double* x)
{
    static double xref[] = {
        // Reference solution vector for Ax = b (len 6)...
        0.1479665631498538,
        0.1623141664502468,
        0.008463367436900621,
        0.03391852175929072,
        0.055050669463981176,
        0.11444116927844857
    };
    memcpy(x, xref, 6*sizeof(double));
}

int main(void)
{
    vecmat_t* A    = dense_malloc_vecmat(6, 6);
    vecmat_t* xref = malloc_bandmat(6, 1);
    vecmat_t* x    = malloc_bandmat(6, 1);

    // Get problem data
    get_Aref(A->data);
    get_xref(xref->data);
    get_bref(x->data);

    // Extract to band, factor, solve
    vecmat_t* P = dense_to_band(A, 2);
    bandmat_factor(P);
    bandmat_solve(P, x->data);

    // Check residual
    for (int i = 0; i < 6; ++i)
        x->data[i] -= xref->data[i];
    assert(vecmat_norm(x) < 1e-8);
    
    free_vecmat(P);
    free_vecmat(x);
    free_vecmat(xref);
    free_vecmat(A);
    return 0;
}
