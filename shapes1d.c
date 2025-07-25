#include "shapes1d.h"

void shapes1d(double* N, double x, int degree)
{
    if (degree == 1) {
        N[0] = 0.5*(1-x);
        N[1] = 0.5*(1+x);
    } else if (degree == 2) {
        N[0] = -0.5*(1-x)*x;
        N[1] =      (1-x)*  (1+x);
        N[2] =  0.5*      x*(1+x);
    } else if (degree == 3) {
        N[0] = (-1.0/16) * (1-x)*(1-3*x)*(1+3*x);
        N[1] = ( 9.0/16) * (1-x)*(1-3*x)*(1+x);
        N[2] = ( 9.0/16) * (1-x)*(1+3*x)*(1+x);
        N[3] = (-1.0/16) * (1-3*x)*(1+3*x)*(1+x);
    }
}

void dshapes1d(double* dN, double x, int degree)
{
    if (degree == 1) {
        dN[0] = -0.5;
        dN[1] =  0.5;
    } else if (degree == 2) {
        dN[0] = -0.5*(1-2*x);
        dN[1] = -2*x;
        dN[2] =  0.5*(1+2*x);
    } else if (degree == 3) {
        dN[0] = 1.0/16 * ( 1+x*( 18+x*-27));
        dN[1] = 9.0/16 * (-3+x*(-2+x* 9));
        dN[2] = 9.0/16 * ( 3+x*(-2+x*-9));        
        dN[3] = 1.0/16 * (-1+x*( 18+x* 27));
    }
}
