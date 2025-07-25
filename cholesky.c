#include <math.h>

// Compute Cholesky of n-by-n packed A with bandwidth bw
void band_cholesky(double* PA, int n, int bw)
{
    for (int k = 0; k < n; ++k) {

        // Compute kth diagonal element
        PA[k] = sqrt(PA[k]);         

        // Scale across the row
        for (int j = k+1; j < n && j <= k+bw; ++j)
            PA[j+n*(j-k)] /= PA[k];

        // Apply the Schur complement update
        for (int j = k+1; j < n && j <= k+bw; ++j)
            for (int i = k+1; i <= j; ++i)
                PA[j+n*(j-i)] -= PA[i+n*(i-k)]*PA[j+n*(j-k)];                
    }
}

// Overwrite input variable x with R \ (R^T \ x)
void bcholesky_solve(double* PR, double* x, int n, int bw)
{
    // Forward substitution
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int dj = 1; dj <= bw && dj <= i; ++dj)
            bi -= PR[i+dj*n]*x[i-dj];
        x[i] = bi/PR[i];
    }

    // Backward substitution
    for (int i = n-1; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j <= i+bw && j < n; ++j)        
            yi -= PR[j+(j-i)*n]*x[j];
        x[i] = yi/PR[i];
    }
}
