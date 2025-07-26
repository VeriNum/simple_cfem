#ifndef ELEMENT_H
#define ELEMENT_H

struct fem_t;
struct assemble_t;

typedef struct element_t {
    void *p; // Context pointer
    void (*add)(void* p, struct fem_t* fe, int eltid,
                double* R, struct assemble_t* K);
    void (*free)(void* p);
} element_t;

element_t* malloc_poisson_element();
void free_element(element_t* e);

void element_add(element_t* e, struct fem_t* fe, int eltid,
                 double* R, struct assemble_t* K);

#endif /* ELEMENT_H */
