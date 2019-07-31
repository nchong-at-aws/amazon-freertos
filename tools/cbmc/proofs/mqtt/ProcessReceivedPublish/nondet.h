#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * Non-determinstic functions used in CBMC proofs
 */
size_t nondet_size_t();
int nondet_int();
uint8_t nondet_uint8_t();
bool nondet_bool();
void *nondet_voidp();
uint32_t nondet_uint32_t();
uint64_t nondet_uint64_t();
