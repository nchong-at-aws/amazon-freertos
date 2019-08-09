/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS+TCP includes. */
#include "iot_https_client.h"
#include "iot_https_internal.h"

#include "../global_state_HTTP.c"

/* The function under test */
void _sendHttpsRequest( IotTaskPool_t pTaskPool,
			IotTaskPoolJob_t pJob,
			void * pUserContext );

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

#if __has_builtin(__builtin___sprintf_chk)
int __builtin___snprintf_chk (char *buf, size_t size, int flag, size_t os,
			      const char *fmt, ...)
{
  int ret;
  __CPROVER_assert(__CPROVER_w_ok(buf, size), "sprintf output writeable");
  __CPROVER_assert(fmt, "sprintf format nonnull");
  __CPROVER_assume(ret >= 0 && ret <= HTTPS_MAX_CONTENT_LENGTH_LINE_LENGTH);
  return ret;
}
#else
int snprintf(char *buf, size_t size, const char *fmt, ...)
{
  int ret;
  __CPROVER_assert(__CPROVER_w_ok(buf, size), "sprintf output writeable");
  __CPROVER_assert(fmt, "sprintf format nonnull");
  __CPROVER_assume(ret >= 0 && ret <= HTTPS_MAX_CONTENT_LENGTH_LINE_LENGTH);
  return ret;
}
#endif

void harness() {
  IotTaskPool_t pTaskPool;
  IotTaskPoolJob_t pJob;
  IotHttpsRequestHandle_t reqHandle = allocate_IotRequestHandle();
  __CPROVER_assume(reqHandle);
  __CPROVER_assume(reqHandle->pHttpsConnection);
  __CPROVER_assume(reqHandle->pHttpsResponse);

  initialize_IotRequestHandle(reqHandle);
  initialize_IotConnectionHandle(reqHandle->pHttpsConnection);
  initialize_IotResponseHandle(reqHandle->pHttpsResponse);

  IotHttpsResponseHandle_t respHandle1 = allocate_IotResponseHandle();
  __CPROVER_assume(respHandle1);
  initialize_IotResponseHandle(respHandle1);
  IotListDouble_InsertHead(&reqHandle->pHttpsConnection->respQ, &respHandle1->link);

  IotHttpsRequestHandle_t reqHandle1 = allocate_IotRequestHandle();
  __CPROVER_assume(reqHandle1);
  initialize_IotRequestHandle(reqHandle1);
  IotListDouble_InsertHead(&reqHandle->pHttpsConnection->reqQ, &reqHandle1->link);

  __CPROVER_assume(is_stubbed_IotRequestHandle(reqHandle));
  __CPROVER_assume(is_valid_IotRequestHandle(reqHandle));
  __CPROVER_assume(is_valid_IotConnectionHandle(reqHandle->pHttpsConnection));
  __CPROVER_assume(is_valid_IotResponseHandle(reqHandle->pHttpsResponse));

  __CPROVER_assume(is_stubbed_NetworkInterface(reqHandle->pHttpsConnection->pNetworkInterface));


  _sendHttpsRequest(pTaskPool, pJob, (void *)reqHandle);
}
