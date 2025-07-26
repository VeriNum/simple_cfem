#ifndef VECMAT_H
#define VECMAT_H

typedef struct vecmat_head_t {
    int m, n;
    double data[1];
} vecmat_head_t;

double* malloc_vecmat(int m, int n);
void free_vecmat(double* data);

vecmat_head_t* vecmat(double* data);
void vecmat_clear(double* data);
void vecmat_print(double* data);
double vecmat_norm2(double* data);
double vecmat_norm(double* data);

#endif /* VECMAT_H */
