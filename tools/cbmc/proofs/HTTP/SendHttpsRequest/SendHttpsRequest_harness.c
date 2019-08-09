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

  // ???: Sarena: this section is highly questionable!
  IotHttpsResponseHandle_t respHandle1 = allocate_IotResponseHandle();
  __CPROVER_assume(respHandle1);
  initialize_IotResponseHandle(respHandle1);
  IotListDouble_InsertHead(&reqHandle->pHttpsResponse->link, &respHandle1->link);

  __CPROVER_assume(is_stubbed_IotRequestHandle(reqHandle));
  __CPROVER_assume(is_valid_IotRequestHandle(reqHandle));
  __CPROVER_assume(is_valid_IotConnectionHandle(reqHandle->pHttpsConnection));
  __CPROVER_assume(is_valid_IotResponseHandle(reqHandle->pHttpsResponse));

  __CPROVER_assume(is_stubbed_NetworkInterface(reqHandle->pHttpsConnection->pNetworkInterface));


  _sendHttpsRequest(pTaskPool, pJob, (void *)reqHandle);
}
