/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS+TCP includes. */
#include "iot_https_client.h"
#include "iot_https_internal.h"

#include "../global_state_HTTP.c"

/****************************************************************
* Stub out memcpy so that it copies nothing but simply checks that the
* arguments are readable and writeable.
*
* A sequence of memcpy's in _addHeader causes cbmc to generate an
* enormous formula with 229M+ clauses.  The values copies are never
* used.
*
* MacOS header file /usr/include/secure/_string.h defines memcpy to
* use a builtin function supported by CBMC, so we stub out the builtin
* memcpy instead of the standard memcpy.
****************************************************************/

/* This is a clang macro not available on linux */
#ifndef __has_builtin
#define __has_builtin(x) 0
#endif

#if __has_builtin(__builtin___memcpy_chk)
void *__builtin___memcpy_chk(void *dest, const void *src, size_t n, size_t m) {
  __CPROVER_assert(__CPROVER_w_ok(dest, n), "write");
  __CPROVER_assert(__CPROVER_r_ok(src, n), "read");
  return dest;
}
#else
void *memcpy(void *dest, const void *src, size_t n) {
  __CPROVER_assert(__CPROVER_w_ok(dest, n), "write");
  __CPROVER_assert(__CPROVER_r_ok(src, n), "read");
  return dest;
}
#endif

// function under test
void _networkReceiveCallback( void * pNetworkConnection,
                                     void * pReceiveContext );

void harness() {
  void *pNetworkConnection = NULL;
  IotHttpsConnectionHandle_t pReceiveContext = allocate_IotConnectionHandle();
  __CPROVER_assume(pReceiveContext);
  initialize_IotConnectionHandle(pReceiveContext);
  __CPROVER_assume(is_valid_IotConnectionHandle(pReceiveContext));
  __CPROVER_assume(is_stubbed_NetworkInterface(pReceiveContext->pNetworkInterface));
  _networkReceiveCallback(pNetworkConnection, (void *)pReceiveContext);
}
