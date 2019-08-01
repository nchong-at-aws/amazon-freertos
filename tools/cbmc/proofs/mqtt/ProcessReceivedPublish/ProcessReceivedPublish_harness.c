/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "aws_mqtt_lib.h"

#include "util.h"
#include "nondet.h"
#include "mqtt_type.h"

void prvProcessReceivedPublish(MQTTContext_t *pxMQTTContext);


///* Abstract function after removing static attributed. */
//MQTTBool_t prvInvokeSubscriptionCallbacks(MQTTContext_t * pxMQTTContext,
//					  const MQTTPublishData_t * pxPublishData,
//					  MQTTBool_t * pxSubscriptionCallbackInvoked )
//{
//}
//

/****************************************************************/


void harness() {
  MQTTContext_t *pxMQTTContext = newMQTTContext(NULL);
  // how write precondition postconditions
  __CPROVER_assume(pxMQTTContext);
  __CPROVER_assume(pxMQTTContext->xRxBuffer);

  prvProcessReceivedPublish(pxMQTTContext);
}

