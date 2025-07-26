#include <math.h>
#include <assert.h>

#include "shapes1d.h"

double test_shapes1d()
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
    return err;
}

double test_dshapes1d()
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
    return err;
}

int main()
{
    assert(test_shapes1d() < 1e-8);
    assert(test_dshapes1d() < 1e-8);
    return 0;
}
