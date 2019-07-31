#pragma once

#include <stdlib.h>

#define IMPLIES(a, b) (!(a) || (b))

/* This should be fined in the Makefile.common and used with --object-bits */
#define CBMC_OBJECT_BITS (4)

/*
 * CBMC has an internal representation in which each object has an
 * index and a (signed) offset A buffer cannot be larger than the max
 * size of the offset The Makefile is expected to set CBMC_OBJECT_BITS
 * to the value of --object-bits
 */
#define MAX_MALLOC (SIZE_MAX >> (CBMC_OBJECT_BITS + 1))

/**
 * CBMC model of calloc always succeeds, even if the requested size is larger
 * than CBMC can internally represent.  This function does a
 *     __CPROVER_assume(size <= MAX_MALLOC);
 * before calling calloc, and hence will never return an invalid pointer.
 */
void *bounded_calloc(size_t size);

/**
 * CBMC model of malloc always succeeds, even if the requested size is larger
 * than CBMC can internally represent.  This function does a
 *     __CPROVER_assume(size <= MAX_MALLOC);
 * before calling malloc, and hence will never return an invalid pointer.
 */
void *bounded_malloc(size_t size);

/**
 * CBMC model of calloc never returns NULL, which can mask bugs in C
 * programs. Thus function:
 * 1) Deterministically returns NULL if more memory is requested than
 *    CBMC can represent
 * 2) Nondeterminstically returns either valid memory or NULL otherwise
 */
void *can_fail_calloc(size_t num, size_t size);

/**
 * CBMC model of malloc never returns NULL, which can mask bugs in C
 * programs. Thus function:
 * 1) Deterministically returns NULL if more memory is requested than
 *    CBMC can represent
 * 2) Nondeterminstically returns either valid memory or NULL otherwise
 */
void *can_fail_malloc(size_t size);

/**
 * CBMC model of realloc never returns NULL, which can mask bugs in C
 * programs. Thus function:
 * 1) Deterministically returns NULL if more memory is requested than
 *    CBMC can represent
 * 2) Does the full range of valid behaviours if (newsize == 0)
 * 3) Nondeterminstically returns either valid memory or NULL otherwise
 */
void *can_fail_realloc(void *ptr, size_t newsize);
