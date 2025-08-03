#include <math.h>
#include <assert.h>

#include "quadrules.h"

int main()
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
    return 0;
}
