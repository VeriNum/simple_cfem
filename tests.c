#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#include "bandmat.h"
#include "assemble.h"
#include "gaussquad.h"
#include "shapes1d.h"
#include "fem.h"
#include "element.h"

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

void test_band_cholesky()
{
    double A[36], b[6];
    get_Aref(A);
    get_bref(b);
    bandmat_t* BA = dense_to_band(A, 6, 2);
    bandmat_factor(BA);
    bandmat_solve(BA, b);
    printf("Check that band Cholesky in band storage works: %g\n",
           check_solution(b));
    free_bandmat(BA);
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
    assemble_t assembler;
    bandmat_t* A = malloc_bandmat(6, 2);
    init_assemble_band(&assembler, A);

    // Element matrix template
    double emat[4] = {1.0, -1.0, -1.0, 1.0};

    // Assembly loop
    for (int i = 0; i < 7; ++i) {
        assemble_add(&assembler, emat, ids+2*i, 2);
    }

    // Check the band matrix
    double err = 0.0;
    for (int j = 0; j < 6; ++j)
        err += (A->P[j]-2.0)*(A->P[j]-2.0);
    for (int j = 1; j < 6; ++j)
        err += (A->P[j+6]+1.0)*(A->P[j+6]+1.0);
    err = sqrt(err);
    printf("Check on band assembler: %g\n", err);

    // Clean up
    free_bandmat(A);
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

void test_shapes1d()
{
    double N[4];
    double err = 0.0;
    for (int d = 1; d <= 3; ++d) {
        for (int j = 0; j <= d; ++j) {

            // Evaluate at the ith nodal point
            double xj = -1.0 + 2.0*j/d;
            shapes1d(N, xj, d);

            // Check that these are Lagrange functions (Ni(xj) = delta_ij)
            N[j] -= 1.0;
            for (int i = 0; i <= d; ++i)
                err += N[i]*N[i];

        }
    }
    err = sqrt(err);
    printf("Check correctness of 1D shape functions: %g\n", err);
}

void test_dshapes1d()
{
    double Np[4], Nm[4], dN[4];
    double xtest = 0.707107;
    double err = 0.0;
    double h = 1e-6;

    for (int d = 1; d <= 3; ++d) {

        // Evaluate near the test point
        shapes1d(Np, xtest+h, d);
        shapes1d(Nm, xtest-h, d);
        dshapes1d(dN, xtest, d);

        // Finite difference check
        for (int i = 0; i <= d; ++i) {
            double dNi_fd = (Np[i]-Nm[i])/2/h;
            double err_i  = dNi_fd - dN[i];
            err += err_i*err_i;
        }
    }
    err = sqrt(err);
    printf("Check correctness of 1D shape derivs vs fd: %g\n", err);
}

void test_mesh_setup()
{
    fem_t* fe = malloc_fem(6, 1);

    // Set up the mesh
    fem_mesh(fe, 0.0, 1.0);
    fe->id[0]           = -1;
    fe->id[fe->numnp-1] = -1;
    fe->U[fe->numnp-1] = 1.0;
    int nactive = fem_assign_ids(fe);
    fem_print(fe);

    // Attach an element type to the mesh
    fe->etype = malloc_poisson_element();

    // Set up element and assembly space;
    double* R = (double*) malloc(nactive * sizeof(double));
    bandmat_t* K = malloc_bandmat(nactive, 1);

    // Assemble system
    fem_assemble_band(fe, R, K);

    // Print system
    printf("K matrix:\n");
    bandmat_print(K);
    printf("R vector:\n");
    for (int i = 0; i < nactive; ++i)
        printf("%g\n", R[i]);

    // Factor and solve
    bandmat_factor(K);
    bandmat_solve(K, R);
    printf("Solution vector:\n");
    for (int i = 0; i < nactive; ++i)
        printf("%g\n", R[i]);

    free_bandmat(K);
    free(R);
    free_element(fe->etype);
    free_fem(fe);
}

int main()
{
    test_check_solution();
    test_band_cholesky();
    test_band_assembler();
    test_gauss();
    test_shapes1d();
    test_dshapes1d();
    test_mesh_setup();
    return 0;
}
