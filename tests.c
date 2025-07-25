#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#include "cholesky.h"
#include "band_assemble.h"
#include "gaussquad.h"

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

double check_solution(double* x)
{
    double A[36], b[6];

    get_Aref(A);
    get_bref(b);
    for (int j = 0; j < 6; ++j)
        for (int i = 0; i < 6; ++i)
            b[i] -= A[i+6*j]*x[j];

    double rnorm = 0.0;
    for (int j = 0; j < 6; ++j)
        rnorm += b[j]*b[j];

    return sqrt(rnorm);
}

void test_check_solution()
{
    double x[6];
    get_xref(x);
    printf("Check that reference solution is good / tester works: ");
    printf("%g\n", check_solution(x));
}

// Convert dense n-by-n A to band matrix P with bandwidth bw
void dense_to_band(double* A, double* P, int n, int bw)
{
    for (int d = 0; d <= bw; ++d)
        for (int j = d; j < n; ++j) {
            int i = j-d;
            P[j+d*n] = A[i+j*n];
        }
}

void test_band_cholesky()
{
    double A[36], PA[18], b[6];
    get_Aref(A);
    get_bref(b);
    dense_to_band(A, PA, 6, 2);
    band_cholesky(PA, 6, 2);
    bcholesky_solve(PA, b, 6, 2);
    printf("Check that band Cholesky in band storage works: %g\n",
           check_solution(b));    
}

void test_band_assembler()
{
    // Set up element connectivity
    int ids[14] = {
        -1, 0,
        0, 1,
        1, 2,
        2, 3,
        3, 4,
        4, 5,
        5, -2};

    // Set up assembly
    double PA[6*2];
    band_assembler_t assembler;
    memset(PA, 0, 6*2*sizeof(double));
    assembler.P = PA;
    assembler.n = 6;
    assembler.b = 1;

    // Element matrix template
    double emat[4] = {1.0, -1.0, -1.0, 1.0};

    // Assembly loop
    for (int i = 0; i < 7; ++i) {
        add_to_band(&assembler, emat, ids+2*i, 2);
    }

    // Check the band matrix
    double err = 0.0;
    for (int j = 0; j < 6; ++j)
        err += (PA[j]-2.0)*(PA[j]-2.0);
    for (int j = 1; j < 6; ++j)
        err += (PA[j+6]+1.0)*(PA[j+6]+1.0);
    err = sqrt(err);
    printf("Check on band assembler: %g\n", err);
}

void test_gauss()
{
    // Should be exact on polynomials of degree 2k-1
    // Test on x^5 + 3x^4 - x^3 + x^2 + x + 1
    //    (true integral: 6/5 + 2/3 + 2)
    double Iref = 6.0/5.0 + 2.0/3.0 + 2.0;
    double I = 0.0;
    printf("Check Gauss quadrature for 3-10 points: ");
    for (int npts = 3; npts < 10; ++npts) {
        I = 0.0;
        for (int i = 0; i < npts; ++i) {
            double xi = gauss_point(i, npts);
            double wi = gauss_weight(i, npts);
            double pxi = ((((xi+3)*xi-1)*xi+1)*xi+1)*xi+1;
            I += pxi*wi;
        }
        printf(" %.2e", I-Iref);
    }
    printf("\n");
}

int main()
{
    test_check_solution();
    test_band_cholesky();
    test_band_assembler();
    test_gauss();
    return 0;
}
