#ifndef ASSEMBLE_H
#define ASSEMBLE_H

//ldoc on
/**
 * ## Assembly
 * 
 * Each element in a finite element discretization consists of
 * 
 * - A domain $\Omega_e$ for the $e$th element, and
 * - Local shape functions $N^e_1, \ldots, N^e_m$, which are often
 *   Lagrange functions for interpolation at some set of nodes
 *   in $\Omega_e$.
 * 
 * Each local shape function $N^e_j$ on the domain $\Omega_e$ is the
 * restriction of some global shape function $N_{j'}$ on the whole
 * domain $\Omega$.  Usually we only work explicitly with the local
 * functions $N^e_j$; the global functions are implicit.
 * 
 * *Assembly* is the process of reconstructing a quantity defined in
 * terms of global shape functions from the contributions of the
 * individual elements and their local shape functions.  For example,
 * to compute
 * $$
 *   F_i = \int_{\Omega} f(x) N_i(x) \, dx,
 * $$
 * we rewrite the integral as
 * $$
 *   F_i = \int_{\Omega_e} \sum_{i \sim i'} f(x) N^e_{i'}(x) \, dx.
 * $$
 * In code, this is separated into two pieces:
 * 
 * - Compute element contributions $\int_{\Omega_e} f(x) N^e_{i'}(x) \, dx$.
 *   This is the responsibility of the element implementation.
 * - Sum contributions into the global position $i$ corresponding to
 *   the element-local index $i'$.  This is managed by an assembly loop.
 * 
 * The concept of an "assembly loop" is central to finite element methods,
 * but it is not unique to this setting.  For example, circuit simulators
 * similarly construct system matrices (conductance, capacitance, etc)
 * via the contributions of circuit elements (resistors, capacitors,
 * inductors, and so forth).
 * 
 * We have two types of assembly loops that we care about: those that
 * involve pairs of shape functions and result in matrices, and
 * those that explicitly involve only a single shape function and result
 * in vectors.
 * 
 * We will sometimes also want to discard some element contributions
 * that correspond to interactions with shape functions associated with
 * known boundary values (for example).  We also handle this filtering
 * work as part of our assembly process.
 * 
 * ### Matrix assemblers
 * 
 * There are several matrix formats that we might want to target as
 * outputs for assembling a matrix; these include dense storage,
 * banded storage, coordinate form, or CSR.  Because we would like
 * to re-use the same assembly loop logic with these different formats,
 * we define an abstract `assemble_t` interface with two basic methods:
 * 
 * - `add(assembler, ematrix, ids, ne)` adds the `ne`-by-`ne` element
 *   matrix (`ematrix`) into the global structure referenced by the
 *   assembler.  The `ids` array maps from local indices to global
 *   indicies (i.e. `ids[ilocal] = iglobal`).
 * - `clear(assembler)` zeros out the matrix storage in preparation
 *   for assembly of a new matrix.
 * 
 */
// Interface for general assembler object (callback + context)
typedef struct assemble_t {
    void* p;                                // Context
    void (*add)(void*, double*, int*, int); // Add contribution
    void (*clear)(void*);                   // Clear
} assemble_t;

// Convenience functions that call the assembler methods
void assemble_add(assemble_t* assembler, double* emat, int* ids, int ne);
void assemble_clear(assemble_t* assembler);

/**
 * We currently only support two types of assemblers: dense and band.
 * In all cases, we assume that the dimension `n` of the matrix
 * is big enough (all active indices are less than `n`).  For the
 * band assembler, we do check to make sure there are no contributions
 * that are outside the band (and error out if a contribution does live
 * outside the expected band).
 * 
 * Both the dense and the band matrix expect pointers to data using
 * our `vecmat_t` scheme, so we do not need to pass in explicit
 * dimension arguments.
 * 
 */
void init_assemble_dense(assemble_t* assembler, double* A);
void init_assemble_band(assemble_t* assembler, double* b);

/**
 * ### Vector assembly
 * 
 * We only really use one vector representation (a simple array), so
 * there is no need for the same type of assembler abstraction for vectors
 * that we have for matrices.  The semantics of `assemble_vector` are
 * similar to those of `assemble_add` in the matrix case, except now
 * we add the element vector `ve` into the global vector `v`.
 * 
 */
void assemble_vector(double* v, double* ve, int* ids, int ne);

//ldoc off
#endif /* ASSEMBLE_H */
