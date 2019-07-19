/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "aws_mqtt_lib.h"


void prvProcessReceivedPublish(MQTTContext_t *pxMQTTContext);


/* Abstract function after removing static attributed. */
MQTTBool_t prvInvokeSubscriptionCallbacks(MQTTContext_t * pxMQTTContext,
					  const MQTTPublishData_t * pxPublishData,
					  MQTTBool_t * pxSubscriptionCallbackInvoked ) {
  MQTTBool_t bool;
  return(bool);
}


/****************************************************************/


/* abstract call backs */
MQTTBool_t nullCallback(void * pvCallbackContext,
			const MQTTEventCallbackParams_t * const pxParams) {
  MQTTBool_t bool;
  return(bool);
};
char nullCallbackContext[1];

/****************************************************************/

struct MqttBuffer {
  MQTTBufferMetadata_t Metadata;
  uint8_t data[100];
};

struct MqttBuffer *myMqttBuffer(struct MqttBuffer *buffer) {
  if (buffer == NULL)
    buffer = malloc(sizeof(struct MqttBuffer));
  buffer->Metadata.xLink.pxPrev = &(buffer->Metadata.xLink);
  buffer->Metadata.xLink.pxNext = &(buffer->Metadata.xLink);
  /* should make this arbitrary sizeof(metadata) + 0 to 100 */
  buffer->Metadata.ulBufferLength = sizeof(struct MqttBuffer);
  /* should make this arbitrary 0 to 100 within effective buffer length */
  buffer->Metadata.ulDataLength =
    sizeof(struct MqttBuffer) - sizeof(MQTTBufferMetadata_t);
  return(buffer);
}

/****************************************************************/

MQTTContext_t *myMQTTContext() {
  MQTTContext_t * context = malloc(sizeof(MQTTContext_t));
  context->pxCallback = nullCallback;
  context->pvCallbackContext = nullCallbackContext;

  context->xRxBuffer = (void *)myMqttBuffer(NULL);
  __CPROVER_assume(1 <= context->xRxMessageState.ucRemaingingLengthFieldBytes);
  __CPROVER_assume(context->xRxMessageState.ucRemaingingLengthFieldBytes <= 4);
  context->pvSendContext = malloc(sizeof(UBaseType_t));
  context->pxMQTTSendFxn = malloc(sizeof(MQTTSend_t));
  context->pxCallback = malloc(sizeof(MQTTEventCallback_t));
  listINIT_HEAD(&(context->xTxBufferListHead));
  listADD(&(context->xTxBufferListHead), &mqttbufferGET_LINK(myMqttBuffer(NULL)));
  listADD(&(context->xTxBufferListHead), &mqttbufferGET_LINK(myMqttBuffer(NULL)));
  context->xBufferPoolInterface.pxGetBufferFxn = malloc(sizeof(MQTTGetFreeBuffer_t));
  context->xBufferPoolInterface.pxReturnBufferFxn = malloc(sizeof(MQTTReturnBuffer_t));
  return(context);



}

/****************************************************************/


void harness() {

  MQTTContext_t *pxMQTTContext = myMQTTContext();
  prvProcessReceivedPublish(pxMQTTContext);
}


  //__CPROVER_assume(pxMQTTContext->xRxMessageState.ulTotalMessageLength == 1024);

/*We need the global state for this proof. What should be the size of the buffer pxMQTTContext->xRxBuffer
how much memory this pointer should be able to access? What should be the size of
xEventCallbackParams.u.xPublishData.usTopicLength, pxMQTTContext->xRxMessageState.ulTotalMessageLength,
pxMQTTContext->xRxMessageState.ucRemaingingLengthFieldBytes. What is the state of free buffer pool? */
