#include <stdio.h>
#include <math.h>
#include <assert.h>

#include "quadrules.h"

void test_gauss1d(void)
{
    // Should be exact on polynomials of degree 2k-1
    // Test on x^5 + 3x^4 - x^3 + x^2 + x + 1
    //    (true integral: 6/5 + 2/3 + 2)
    double Iref = 6.0/5.0 + 2.0/3.0 + 2.0;
    double I = 0.0;

    for (int npts = 3; npts < 10; ++npts) {
        I = 0.0;
        for (int i = 0; i < npts; ++i) {
            double xi = gauss_point(i, npts);
            double wi = gauss_weight(i, npts);
            double pxi = ((((xi+3)*xi-1)*xi+1)*xi+1)*xi+1;
            I += pxi*wi;
        }
        assert(fabs(I-Iref) < 1e-8);
    }
}

void test_gauss2d(void)
{
    for (int d = 1; d < 5; ++d) {
        int npts = d*d;
        double Iref[] = {4.0, 0.0, 0.0, 0.0};
        for (int pxy = 0; pxy < 4; ++pxy) {
            int px = pxy%2;
            int py = pxy/2;

            // Compute integral and check (should be exact on bilinear)
            double I = 0.0;
            for (int i = 0; i < npts; ++i) {
                double xi[2];
                gauss2d_point(xi, i, npts);
                double w = gauss2d_weight(i, npts);
                double fx = (px ? xi[0] : 1.0) * (py ? xi[1] : 1.0);
                I += fx*w;
            }
            assert(fabs(I-Iref[pxy]) < 1e-8);
        }
    }
}

void test_hughes(void)
{
    int npts = 3;
    double Iref[] = {0.5, 1.0/6, 1.0/6, 1.0/24};
    for (int pxy = 0; pxy < 4; ++pxy) {
        int px = pxy%2;
        int py = pxy/2;

        // Compute integral and check (should be exact on bilinear)
        double I = 0.0;
        for (int i = 0; i < npts; ++i) {
            double xi[2];
            hughes_point(xi, i, npts);
            double w = hughes_weight(i, npts);
            double fx = (px ? xi[0] : 1.0) * (py ? xi[1] : 1.0);
            I += fx*w;
        }
        assert(fabs(I-Iref[pxy]) < 1e-8);
    }
}

int main(void)
{
    test_gauss1d();
    test_gauss2d();
    test_hughes();
    return 0;
}
