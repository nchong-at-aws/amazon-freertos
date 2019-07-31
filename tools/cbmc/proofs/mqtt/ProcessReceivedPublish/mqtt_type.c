#include "FreeRTOS.h"
#include "aws_mqtt_lib.h"

/****************************************************************
 * MqttBuffer
 ****************************************************************/

#ifndef MQTT_BUFFER_USER_DATA_LENGTH
  #define MQTT_BUFFER_USER_DATA_LENGTH 100
#endif

struct MqttBuffer {
  MQTTBufferMetadata_t Metadata;
  uint8_t data[MQTT_BUFFER_USER_DATA_LENGTH];
};

struct MqttBuffer *newMqttBuffer(struct MqttBuffer *buffer) {
  if (buffer == NULL)
    buffer = malloc(sizeof(struct MqttBuffer));

  if (buffer) {
    // A transmit or receive buffer comes from a doubly linked buffer pool.
    // Initialize the links
    buffer->Metadata.xLink.pxPrev = &(buffer->Metadata.xLink);
    buffer->Metadata.xLink.pxNext = &(buffer->Metadata.xLink);

    /* should make this arbitrary sizeof(metadata) + 0 to 100 */
    buffer->Metadata.ulBufferLength = sizeof(struct MqttBuffer);
    /* should make this arbitrary 0 to 100 within effective buffer length */
    buffer->Metadata.ulDataLength =
      sizeof(struct MqttBuffer) - sizeof(MQTTBufferMetadata_t);
  }

  return buffer;
}

/****************************************************************
 * MQTTContext_t
 ****************************************************************/

MQTTBool_t nullCallback(void *pvCallbackContext,
			const MQTTEventCallbackParams_t *const pxParams) {
  MQTTBool_t bool;
  return(bool);
};

Link_t *newTxBufferList(Link_t *head, size_t size) {
  if (!head)
    head = malloc(sizeof(Link_t));
  listINIT_HEAD(head);
  for (int i = 0; i < size; i++)
    listADD(head, &mqttbufferGET_LINK(newMqttBuffer(NULL)));
  return head;
}

MQTTContext_t *newMQTTContext() {
  MQTTContext_t *context = malloc(sizeof(MQTTContext_t));
  context->pxCallback = nullCallback;
  context->pvCallbackContext = malloc(1);

  /* receive buffer containing the message being parsed */
  context->xRxBuffer = newMqttBuffer(NULL);
  __CPROVER_assume(1 <= context->xRxMessageState.ucRemaingingLengthFieldBytes);
  __CPROVER_assume(context->xRxMessageState.ucRemaingingLengthFieldBytes <= 4);

  /* transmit buffers containing messages waiting for ack */
  newTxBufferList(&(context->xTxBufferListHead), 2);

  context->pvSendContext = malloc(sizeof(UBaseType_t));
  context->pxMQTTSendFxn = malloc(sizeof(MQTTSend_t));
  context->pxCallback = malloc(sizeof(MQTTEventCallback_t));

  context->xBufferPoolInterface.pxGetBufferFxn =
    malloc(sizeof(MQTTGetFreeBuffer_t));
  context->xBufferPoolInterface.pxReturnBufferFxn =
    malloc(sizeof(MQTTReturnBuffer_t));
  return(context);

}
