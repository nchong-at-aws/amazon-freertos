/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "aws_mqtt_lib.h"

#include "util.h"
#include "nondet.h"

void prvProcessReceivedPublish(MQTTContext_t *pxMQTTContext);


/* Abstract function after removing static attributed. */
MQTTBool_t prvInvokeSubscriptionCallbacks(MQTTContext_t * pxMQTTContext,
					  const MQTTPublishData_t * pxPublishData,
					  MQTTBool_t * pxSubscriptionCallbackInvoked )
{
}


/****************************************************************/


void harness() {

  MQTTContext_t *pxMQTTContext = myMQTTContext(NULL);
  prvProcessReceivedPublish(pxMQTTContext);
}

