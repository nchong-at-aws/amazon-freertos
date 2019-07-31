#include <stdint.h>
#include "util.h"

void *bounded_calloc(size_t num, size_t size) {
    size_t required_bytes;
    //__CPROVER_assume(aws_mul_size_checked(num, size, &required_bytes) ==
    //		     AWS_OP_SUCCESS);
    __CPROVER_assume(required_bytes <= MAX_MALLOC);
    return calloc(num, size);
}

void *bounded_malloc(size_t size) {
    __CPROVER_assume(size <= MAX_MALLOC);
    return malloc(size);
}

void *can_fail_calloc(size_t num, size_t size) {
    return nondet_bool() ? NULL : bounded_calloc(num, size);
}

void *can_fail_malloc(size_t size) {
    return nondet_bool() ? NULL : bounded_malloc(size);
}

/**
 * https://en.cppreference.com/w/c/memory/realloc
 * If there is not enough memory, the old memory block is not freed
 * and null pointer is returned.
 *
 * If ptr is NULL, the behavior is the same as calling malloc(new_size).
 *
 * If new_size is zero, the behavior is implementation defined (null
 * pointer may be returned (in which case the old memory block may or
 * may not be freed), or some non-null pointer may be returned that
 * may not be used to access storage).
 */
void *can_fail_realloc(void *ptr, size_t newsize) {
    if (newsize > MAX_MALLOC) {
        return NULL;
    }
    if (newsize == 0) {
        if (nondet_bool()) {
            free(ptr);
        }
        return nondet_voidp();
    }
    return nondet_bool() ? NULL : realloc(ptr, newsize);
}
