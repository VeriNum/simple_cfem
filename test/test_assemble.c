#include <string.h>
#include <assert.h>

#include "densemat.h"
#include "bandmat.h"
#include "assemble.h"

void test_K_setup(assemble_t assembler)
{
    double emat[] = {1.0, -1.0, -1.0, 1.0};
    int ids[2];
    assemble_clear(assembler);
    ids[0] = 0; ids[1] = 1; assemble_add(assembler, emat, ids, 2);
    ids[0] = 1; ids[1] = 2; assemble_add(assembler, emat, ids, 2);
}

void test_Kassembly(void)
{
    densemat_t A = densemat_malloc(3,3);
    bandmat_t P = bandmat_malloc(3,1);
    struct assemble_t assembler;

    memset(A->data, 0xF, 9 * sizeof(double));
    memset(P->data, 0xF, 6 * sizeof(double));

    init_assemble_dense(&assembler, A);
    test_K_setup(&assembler);
    assert(A->data[0] ==  1.0 && A->data[3] == -1.0 && A->data[6] ==  0.0 &&
           A->data[1] ==  0.0 && A->data[4] ==  2.0 && A->data[7] == -1.0 &&
           A->data[2] ==  0.0 && A->data[5] ==  0.0 && A->data[8] ==  1.0);

    init_assemble_band(&assembler, P);
    test_K_setup(&assembler);
    assert(P->data[0] == 1.0 && P->data[1] ==  2.0 && P->data[2] ==  1.0
                       && P->data[4] == -1.0 && P->data[5] == -1.0);

    bandmat_free(P);
    densemat_free(A);
}

void test_Rassembly(void)
{
    densemat_t v = densemat_malloc(3,1);
    double ve[] = {1.0, -1.0};
    int id[2];

    densemat_clear(v);
    id[0] = 0; id[1] = 1; assemble_vector(v->data, ve, id, 2);
    id[0] = 1; id[1] = 2; assemble_vector(v->data, ve, id, 2);
    assert(v->data[0] == 1.0 && v->data[1] == 0.0 && v->data[2] == -1.0);

    densemat_free(v);
}

int main(void)
{
    test_Kassembly();
    test_Rassembly();
    return 0;
}
