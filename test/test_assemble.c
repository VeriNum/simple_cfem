#include <string.h>
#include <assert.h>

#include "vecmat.h"
#include "bandmat.h"
#include "assemble.h"

void test_K_setup(assemble_t* assembler)
{
    double emat[] = {1.0, -1.0, -1.0, 1.0};
    int ids[2];
    assemble_clear(assembler);
    ids[0] = 0; ids[1] = 1; assemble_add(assembler, emat, ids, 2);
    ids[0] = 1; ids[1] = 2; assemble_add(assembler, emat, ids, 2);
}

void test_Kassembly(void)
{
    double* A = malloc_vecmat(3,3);
    double* P = malloc_bandmat(3,1);
    assemble_t assembler;

    memset(A, 0xF, 9 * sizeof(double));
    memset(P, 0xF, 6 * sizeof(double));

    init_assemble_dense(&assembler, A);
    test_K_setup(&assembler);
    assert(A[0] ==  1.0 && A[3] == -1.0 && A[6] ==  0.0 &&
           A[1] ==  0.0 && A[4] ==  2.0 && A[7] == -1.0 &&
           A[2] ==  0.0 && A[5] ==  0.0 && A[8] ==  1.0);

    init_assemble_band(&assembler, P);
    test_K_setup(&assembler);
    assert(P[0] == 1.0 && P[1] ==  2.0 && P[2] ==  1.0
                       && P[4] == -1.0 && P[5] == -1.0);

    free_vecmat(P);
    free_vecmat(A);
}

void test_Rassembly(void)
{
    double* v = malloc_vecmat(3,1);
    double ve[] = {1.0, -1.0};
    int id[2];

    vecmat_clear(v);
    id[0] = 0; id[1] = 1; assemble_vector(v, ve, id, 2);
    id[0] = 1; id[1] = 2; assemble_vector(v, ve, id, 2);
    assert(v[0] == 1.0 && v[1] == 0.0 && v[2] == -1.0);

    free_vecmat(v);
}

int main(void)
{
    test_Kassembly();
    test_Rassembly();
    return 0;
}
