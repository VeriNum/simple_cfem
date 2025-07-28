#include <stddef.h>
#include "shapes.h"

int shapes1dP1(double* N, double* dN, double* xx)
{
    double x = xx[0];
    if (N) {
        N[0] = 0.5*(1-x);
        N[1] = 0.5*(1+x);
    }
    if (dN) {
        dN[0] = -0.5;
        dN[1] =  0.5;
    }
    return 2;
}

int shapes1dP2(double* N, double* dN, double* xx)
{
    double x = xx[0];
    if (N) {
        N[0] = -0.5*(1-x)*x;
        N[1] =      (1-x)*  (1+x);
        N[2] =  0.5*      x*(1+x);
    }
    if (dN) {
        dN[0] = -0.5*(1-2*x);
        dN[1] = -2*x;
        dN[2] =  0.5*(1+2*x);
    }
    return 3;
}

int shapes1dP3(double* N, double* dN, double* xx)
{
    double x = xx[0];
    if (N) {
        N[0] = (-1.0/16) * (1-x)*(1-3*x)*(1+3*x);
        N[1] = ( 9.0/16) * (1-x)*(1-3*x)*(1+x);
        N[2] = ( 9.0/16) * (1-x)*(1+3*x)*(1+x);
        N[3] = (-1.0/16) * (1-3*x)*(1+3*x)*(1+x);
    }
    if (dN) {
        dN[0] = 1.0/16 * ( 1+x*( 18+x*-27));
        dN[1] = 9.0/16 * (-3+x*(-2+x* 9));
        dN[2] = 9.0/16 * ( 3+x*(-2+x*-9));
        dN[3] = 1.0/16 * (-1+x*( 18+x* 27));
    }
    return 4;
}

int shapes2dP1(double* N, double* dN, double* x)
{
    double Nx[2], dNx[2], Ny[2], dNy[2];
    shapes1dP1(Nx, dNx, x+0);
    shapes1dP1(Ny, dNy, x+1);
    if (N) {
        N[0] = Nx[0]*Ny[0];
        N[1] = Nx[1]*Ny[0];
        N[2] = Nx[1]*Ny[1];
        N[3] = Nx[0]*Ny[1];
    }
    if (dN) {
        dN[0] = dNx[0]*Ny[0];  dN[4] = Nx[0]*dNy[0];
        dN[1] = dNx[1]*Ny[0];  dN[5] = Nx[1]*dNy[0];
        dN[2] = dNx[1]*Ny[1];  dN[6] = Nx[1]*dNy[1];
        dN[3] = dNx[0]*Ny[1];  dN[7] = Nx[0]*dNy[1];
    }
    return 4;
}

int shapes2dP2(double* N, double* dN, double* x)
{
    double Nx[3], dNx[3], Ny[3], dNy[3];
    shapes1dP2(Nx, dNx, x+0);
    shapes1dP2(Ny, dNy, x+1);
    if (N) {
        N[0] = Nx[0]*Ny[0];
        N[1] = Nx[1]*Ny[0];
        N[2] = Nx[2]*Ny[0];
        N[3] = Nx[2]*Ny[1];
        N[4] = Nx[2]*Ny[2];
        N[5] = Nx[1]*Ny[2];
        N[6] = Nx[0]*Ny[2];
        N[7] = Nx[0]*Ny[1];
        N[8] = Nx[1]*Ny[1];
    }
    if (dN) {
        dN[0] = dNx[0]*Ny[0];  dN[ 9] = Nx[0]*dNy[0];
        dN[1] = dNx[1]*Ny[0];  dN[10] = Nx[1]*dNy[0];
        dN[2] = dNx[2]*Ny[0];  dN[11] = Nx[2]*dNy[0];
        dN[3] = dNx[2]*Ny[1];  dN[12] = Nx[2]*dNy[1];
        dN[4] = dNx[2]*Ny[2];  dN[13] = Nx[2]*dNy[2];
        dN[5] = dNx[1]*Ny[2];  dN[14] = Nx[1]*dNy[2];
        dN[6] = dNx[0]*Ny[2];  dN[15] = Nx[0]*dNy[2];
        dN[7] = dNx[0]*Ny[1];  dN[16] = Nx[0]*dNy[1];
        dN[8] = dNx[1]*Ny[1];  dN[17] = Nx[1]*dNy[1];
    }
    return 9;
}

int shapes2dS2(double* N, double* dN, double* x)
{
    double Nx[3], dNx[3], Ny[3], dNy[3];
    shapes1dP2(Nx, dNx, x+0);
    shapes1dP2(Ny, dNy, x+1);
    if (N) {
        N[0] = Nx[0]*Ny[0];
        N[1] = Nx[1]*Ny[0];
        N[2] = Nx[2]*Ny[0];
        N[3] = Nx[2]*Ny[1];
        N[4] = Nx[2]*Ny[2];
        N[5] = Nx[1]*Ny[2];
        N[6] = Nx[0]*Ny[2];
        N[7] = Nx[0]*Ny[1];
    }
    if (dN) {
        dN[0] = dNx[0]*Ny[0];  dN[ 8] = Nx[0]*dNy[0];
        dN[1] = dNx[1]*Ny[0];  dN[ 9] = Nx[1]*dNy[0];
        dN[2] = dNx[2]*Ny[0];  dN[10] = Nx[2]*dNy[0];
        dN[3] = dNx[2]*Ny[1];  dN[11] = Nx[2]*dNy[1];
        dN[4] = dNx[2]*Ny[2];  dN[12] = Nx[2]*dNy[2];
        dN[5] = dNx[1]*Ny[2];  dN[13] = Nx[1]*dNy[2];
        dN[6] = dNx[0]*Ny[2];  dN[14] = Nx[0]*dNy[2];
        dN[7] = dNx[0]*Ny[1];  dN[15] = Nx[0]*dNy[1];
    }
    return 8;
}

int shapes2dT1(double* N, double* dN, double* x)
{
    if (N) {
        N[0] = 1-x[0]-x[1];
        N[1] = x[0];
        N[2] = x[1];
    }
    if (dN) {
        dN[0] = -1.0;  dN[3] = -1.0;
        dN[1] =  1.0;  dN[4] =  0.0;
        dN[2] =  0.0;  dN[5] =  1.0;
    }
    return 3;
}
