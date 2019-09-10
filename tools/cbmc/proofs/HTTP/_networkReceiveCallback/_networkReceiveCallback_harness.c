/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS+TCP includes. */
#include "iot_https_client.h"
#include "iot_https_internal.h"

#include "../global_state_HTTP.c"

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

#if 0 // TODO
void stubbed_errorCallback( void * pPrivData,
                IotHttpsRequestHandle_t reqHandle,
                IotHttpsResponseHandle_t respHandle,
                IotHttpsReturnCode_t rc ) {
}

void stubbed_connectionClosedCallback( void * pPrivData,
                IotHttpsConnectionHandle_t connHandle,
                IotHttpsReturnCode_t rc ) {
}

int is_stubbed_ClientCallback(IotHttpsClientCallbacks_t *ccif) {
  return
    ccif->errorCallback == stubbed_errorCallback &&
    ccif->connectionClosedCallback == stubbed_connectionClosedCallback;
}
#endif // TODO

IotHttpsClientCallbacks_t CCIF = { 0 };

void harness() {
  void *pNetworkConnection = NULL; //< irrelevant (unused by function under test)
  IotHttpsConnectionHandle_t pReceiveContext = allocate_IotConnectionHandle();
  initialize_IotConnectionHandle(pReceiveContext);
  __CPROVER_assume(pReceiveContext);
  __CPROVER_assume(is_valid_IotConnectionHandle(pReceiveContext));
  __CPROVER_assume(is_stubbed_NetworkInterface(pReceiveContext->pNetworkInterface));
  bool harness_choice_resp = nondet_bool();
  if (harness_choice_resp) {
    IotHttpsResponseHandle_t resp = allocate_IotResponseHandle();
    __CPROVER_assume(resp);
    __CPROVER_assume(resp->httpParserInfo.responseParser.data);
    __CPROVER_assume(resp->httpParserInfo.parseFunc == http_parser_execute);
    __CPROVER_assume(is_valid_IotResponseHandle(resp));
    // TODO: this is required so that http_parser_execute can set resp->parserState to PARSER_STATE_BODY_COMPLETE
    // to exit the loop in _flushHttpsNetworkData
    ((_httpsResponse_t *)resp->httpParserInfo.responseParser.data) = resp;
    resp->pCallbacks = &CCIF;
    IotListDouble_InsertHead(&pReceiveContext->respQ, &resp->link);
  }
  __CPROVER_assume(IotHttpsClient_Init() == IOT_HTTPS_OK);
  _networkReceiveCallback(pNetworkConnection, (void *)pReceiveContext);
}
