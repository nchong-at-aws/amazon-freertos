/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "aws_mqtt_lib.h"

#include "util.h"
#include "nondet.h"
#include "mqtt_type.h"

void prvProcessReceivedPublish(MQTTContext_t *pxMQTTContext);

/****************************************************************/


void harness() {
  MQTTContext_t *pxMQTTContext = allocate_MQTTContext(NULL);
  __CPROVER_assume(is_valid_MQTTContext(pxMQTTContext));

  prvProcessReceivedPublish(pxMQTTContext);
}

