#include <stddef.h>
#include <densemat.h>
#include "shapes.h"

int shapes1dP1(double* N, double* dN, double* xx)
{
  double x = densematn_get(xx,1,0,0);
  if (N) {
      densematn_set(N,1,0,0, 0.5*(1-x));
      densematn_set(N,1,0,1, 0.5*(1+x));
  }
  if (dN) {
      densematn_set(dN,2,0,0, -0.5);
      densematn_set(dN,2,1,0,  0.5);
  }
  return 2;
}

int shapes1dP2(double* N, double* dN, double* xx)
{
  double x = densematn_get(xx,1,0,0);
    if (N) {
      densematn_set(N,1,0,0, -0.5*(1-x)*x );
      densematn_set(N,1,0,1, (1-x)*  (1+x) );
      densematn_set(N,1,0,2, 0.5* x*(1+x) );
    }
    if (dN) {
      densematn_set(dN,3,0,0, -0.5*(1-2*x) );
      densematn_set(dN,3,1,0, -2*x );
      densematn_set(dN,3,2,0, 0.5*(1+2*x) );
    }
    return 3;
}

int shapes1dP3(double* N, double* dN, double* xx)
{
  double x = densematn_get(xx,1,0,0);
    if (N) {
      densematn_set(N,1,0,0, (-1.0/16) * (1-x)*(1-3*x)*(1+3*x) );
      densematn_set(N,1,0,1, ( 9.0/16) * (1-x)*(1-3*x)*(1+x) );
      densematn_set(N,1,0,2, ( 9.0/16) * (1-x)*(1+3*x)*(1+x) );
      densematn_set(N,1,0,3, (-1.0/16) * (1-3*x)*(1+3*x)*(1+x) );
    }
    if (dN) {
      densematn_set(dN,4,0,0, 1.0/16 * ( 1+x*( 18+x*-27)) );
      densematn_set(dN,4,1,0, 9.0/16 * (-3+x*(-2+x* 9)) );
      densematn_set(dN,4,2,0, 9.0/16 * ( 3+x*(-2+x*-9)) );
      densematn_set(dN,4,3,0, 1.0/16 * (-1+x*( 18+x* 27)) );
    }
    return 4;
}

int shapes2dP1(double* N, double* dN, double* x)
{
    double Nx[2], dNx[2], Ny[2], dNy[2];
    shapes1dP1(Nx, dNx, x+0);
    shapes1dP1(Ny, dNy, x+1);
    if (N) {
      densematn_set(N,1,0,0, densematn_get(Nx,1,0,0)*densematn_get(Ny,1,0,0));
      densematn_set(N,1,0,1, densematn_get(Nx,1,0,1)*densematn_get(Ny,1,0,0));
      densematn_set(N,1,0,2, densematn_get(Nx,1,0,1)*densematn_get(Ny,1,0,1));
      densematn_set(N,1,0,3, densematn_get(Nx,1,0,0)*densematn_get(Ny,1,0,1));
    }
    if (dN) {
      densematn_set(dN,4,0,0, densematn_get(dNx,2,0,0)* densematn_get(Ny,1,0,0) );
      densematn_set(dN,4,0,1, densematn_get(Nx,1,0,0) * densematn_get(dNy,2,0,0) );
      densematn_set(dN,4,1,0, densematn_get(dNx,2,1,0)* densematn_get(Ny,1,0,0) );
      densematn_set(dN,4,1,1, densematn_get(Nx,1,0,1) * densematn_get(dNy,2,0,0) );
      densematn_set(dN,4,2,0, densematn_get(dNx,2,1,0)* densematn_get(Ny,1,0,1) );
      densematn_set(dN,4,2,1, densematn_get(Nx,1,0,1) * densematn_get(dNy,2,1,0) );
      densematn_set(dN,4,3,0, densematn_get(dNx,2,0,0)* densematn_get(Ny,1,0,1) );
      densematn_set(dN,4,3,1, densematn_get(Nx,1,0,0) * densematn_get(dNy,2,1,0) );
    }
    return 4;
}

int shapes2dP2(double* N, double* dN, double* x)
{
    double Nx[3], dNx[3], Ny[3], dNy[3];
    shapes1dP2(Nx, dNx, x+0);
    shapes1dP2(Ny, dNy, x+1);
    if (N) {
      densematn_set(N,1,0,0, densematn_get(Nx,1,0,0)*densematn_get(Ny,1,0,0));      
      densematn_set(N,1,0,1, densematn_get(Nx,1,0,1)*densematn_get(Ny,1,0,0));      
      densematn_set(N,1,0,2, densematn_get(Nx,1,0,2)*densematn_get(Ny,1,0,0));      
      densematn_set(N,1,0,3, densematn_get(Nx,1,0,2)*densematn_get(Ny,1,0,1));      
      densematn_set(N,1,0,4, densematn_get(Nx,1,0,2)*densematn_get(Ny,1,0,2));      
      densematn_set(N,1,0,5, densematn_get(Nx,1,0,1)*densematn_get(Ny,1,0,2));      
      densematn_set(N,1,0,6, densematn_get(Nx,1,0,0)*densematn_get(Ny,1,0,2));      
      densematn_set(N,1,0,7, densematn_get(Nx,1,0,0)*densematn_get(Ny,1,0,1));      
      densematn_set(N,1,0,8, densematn_get(Nx,1,0,1)*densematn_get(Ny,1,0,1));      
    }
    if (dN) {
      densematn_set(dN,9,0,0, densematn_get(dNx,3,0,0)* densematn_get(Ny,1,0,0) );
      densematn_set(dN,9,0,1, densematn_get(Nx,1,0,0) * densematn_get(dNy,3,0,0) );
      densematn_set(dN,9,1,0, densematn_get(dNx,3,1,0)* densematn_get(Ny,1,0,0) );
      densematn_set(dN,9,1,1, densematn_get(Nx,1,0,1) * densematn_get(dNy,3,0,0) );
      densematn_set(dN,9,2,0, densematn_get(dNx,3,2,0)* densematn_get(Ny,1,0,0) );
      densematn_set(dN,9,2,1, densematn_get(Nx,1,0,2) * densematn_get(dNy,3,0,0) );
      densematn_set(dN,9,3,0, densematn_get(dNx,3,2,0)* densematn_get(Ny,1,0,1) );
      densematn_set(dN,9,3,1, densematn_get(Nx,1,0,2) * densematn_get(dNy,3,1,0) );
      densematn_set(dN,9,4,0, densematn_get(dNx,3,2,0)* densematn_get(Ny,1,0,2) );
      densematn_set(dN,9,4,1, densematn_get(Nx,1,0,2) * densematn_get(dNy,3,2,0) );
      densematn_set(dN,9,5,0, densematn_get(dNx,3,1,0)* densematn_get(Ny,1,0,1) );
      densematn_set(dN,9,5,1, densematn_get(Nx,1,0,2) * densematn_get(dNy,3,2,0) );
      densematn_set(dN,9,6,0, densematn_get(dNx,3,0,0)* densematn_get(Ny,1,0,2) );
      densematn_set(dN,9,6,1, densematn_get(Nx,1,0,0) * densematn_get(dNy,3,2,0) );
      densematn_set(dN,9,7,0, densematn_get(dNx,3,0,0)* densematn_get(Ny,1,0,1) );
      densematn_set(dN,9,7,1, densematn_get(Nx,1,0,0) * densematn_get(dNy,3,1,0) );
      densematn_set(dN,9,8,0, densematn_get(dNx,3,1,0)* densematn_get(Ny,1,0,1) );
      densematn_set(dN,9,8,1, densematn_get(Nx,1,0,1) * densematn_get(dNy,3,1,0) );
    }
    return 9;
}

int shapes2dS2(double* N, double* dN, double* x)
{
    double Nx[3], dNx[3], Ny[3], dNy[3];
    shapes1dP2(Nx, dNx, x+0);
    shapes1dP2(Ny, dNy, x+1);
    if (N) {
      densematn_set(N,1,0,0, densematn_get(Nx,1,0,0)*densematn_get(Ny,1,0,0));      
      densematn_set(N,1,0,1, densematn_get(Nx,1,0,1)*densematn_get(Ny,1,0,0));      
      densematn_set(N,1,0,2, densematn_get(Nx,1,0,2)*densematn_get(Ny,1,0,0));      
      densematn_set(N,1,0,3, densematn_get(Nx,1,0,2)*densematn_get(Ny,1,0,1));      
      densematn_set(N,1,0,4, densematn_get(Nx,1,0,2)*densematn_get(Ny,1,0,2));      
      densematn_set(N,1,0,5, densematn_get(Nx,1,0,1)*densematn_get(Ny,1,0,2));      
      densematn_set(N,1,0,6, densematn_get(Nx,1,0,0)*densematn_get(Ny,1,0,2));      
      densematn_set(N,1,0,7, densematn_get(Nx,1,0,0)*densematn_get(Ny,1,0,1));      
    }
    if (dN) {
      densematn_set(dN,8,0,0, densematn_get(dNx,3,0,0)* densematn_get(Ny,1,0,0) );
      densematn_set(dN,8,0,1, densematn_get(Nx,1,0,0) * densematn_get(dNy,3,0,0) );
      densematn_set(dN,8,1,0, densematn_get(dNx,3,1,0)* densematn_get(Ny,1,0,0) );
      densematn_set(dN,8,1,1, densematn_get(Nx,1,0,1) * densematn_get(dNy,3,0,0) );
      densematn_set(dN,8,2,0, densematn_get(dNx,3,2,0)* densematn_get(Ny,1,0,0) );
      densematn_set(dN,8,2,1, densematn_get(Nx,1,0,2) * densematn_get(dNy,3,0,0) );
      densematn_set(dN,8,3,0, densematn_get(dNx,3,2,0)* densematn_get(Ny,1,0,1) );
      densematn_set(dN,8,3,1, densematn_get(Nx,1,0,2) * densematn_get(dNy,3,1,0) );
      densematn_set(dN,8,4,0, densematn_get(dNx,3,2,0)* densematn_get(Ny,1,0,2) );
      densematn_set(dN,8,4,1, densematn_get(Nx,1,0,2) * densematn_get(dNy,3,2,0) );
      densematn_set(dN,8,5,0, densematn_get(dNx,3,1,0)* densematn_get(Ny,1,0,1) );
      densematn_set(dN,8,5,1, densematn_get(Nx,1,0,2) * densematn_get(dNy,3,2,0) );
      densematn_set(dN,8,6,0, densematn_get(dNx,3,0,0)* densematn_get(Ny,1,0,2) );
      densematn_set(dN,8,6,1, densematn_get(Nx,1,0,0) * densematn_get(dNy,3,2,0) );
      densematn_set(dN,8,7,0, densematn_get(dNx,3,0,0)* densematn_get(Ny,1,0,1) );
      densematn_set(dN,8,7,1, densematn_get(Nx,1,0,0) * densematn_get(dNy,3,1,0) );
    }
    return 8;
}

int shapes2dT1(double* N, double* dN, double* x)
{
    if (N) {
      densematn_set(N,1,0,0,  1-densematn_get(x,1,0,0)-densematn_get(x,1,0,1));
      densematn_set(N,1,0,1,  densematn_get(x,1,0,0));
      densematn_set(N,1,0,2,  densematn_get(x,1,0,1));
    }
    if (dN) {
      densematn_set(dN,3,0,0, -1.0); densematn_set(dN,3,0,1, -1.0); 
      densematn_set(dN,3,1,0,  1.0); densematn_set(dN,3,1,1,  0.0); 
      densematn_set(dN,3,2,0,  0.0); densematn_set(dN,3,2,1,  1.0); 
    }
    return 3;
}
