#include "FreeRTOS.h"
#include "aws_mqtt_lib.h"

#include "util.h"
#include "mqtt_type.h"

/****************************************************************
 *  MQTTPublishCallback_t
 ****************************************************************/

#define CALLBACK_CONTEXT_LENGTH 100

MQTTBool_t nullCallback(void *pvCallbackContext,
			const MQTTEventCallbackParams_t *const pxParams) {
  assert(pvCallbackContext);
  assert(pxParams);
  __CPROVER_r_ok(pvCallbackContext, CALLBACK_CONTEXT_LENGTH);
  __CPROVER_r_ok(pxParams, sizeof(MQTTEventCallbackParams_t));
  // write and is_valid predication for params?
  MQTTBool_t bool;
  return(bool);
};

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
// experiment with data[0] and malloc(sizeof(buffer) + unconstrained integer < max_size)

// is valid should check buffer is readable up to buffer size.

struct MqttBuffer *newMqttBuffer(struct MqttBuffer *buffer) {
  if (buffer == NULL)
    buffer = malloc(sizeof(struct MqttBuffer));

  if (buffer) {
    // A transmit or receive buffer comes from a doubly linked buffer pool.
    // Initialize the links
    // this should go into isvalid
    buffer->Metadata.xLink.pxPrev = &(buffer->Metadata.xLink);
    buffer->Metadata.xLink.pxNext = &(buffer->Metadata.xLink);

    // this stuff should go inside isvalid,
    // is valid should check that bufferlength is actually readable

    /* should make this arbitrary sizeof(metadata) + 0 to 100 */
    buffer->Metadata.ulBufferLength = sizeof(struct MqttBuffer);
    /* should make this arbitrary 0 to 100 within effective buffer length */
    buffer->Metadata.ulDataLength =
      sizeof(struct MqttBuffer) - sizeof(MQTTBufferMetadata_t);
  }

  return buffer;
}

/****************************************************************
 * MQTTSubscription_t
 ****************************************************************/

MQTTSubscription_t *allocate_MQTTSubscription(MQTTSubscription_t *sub) {
  if (!sub)
    sub = can_fail_malloc(sizeof(MQTTSubscription_t));
  if (sub) {
    sub->pvPublishCallbackContext = can_fail_malloc(CALLBACK_CONTEXT_LENGTH);
    sub->pxPublishCallback = nullCallback;
  }
  return sub;
}

int is_valid_MQTTSubscription(MQTTSubscription_t *sub) {
  return
    sub &&
    sub->usTopicFilterLength <= mqttconfigSUBSCRIPTION_MANAGER_MAX_TOPIC_LENGTH
    &&
    sub->pxPublishCallback &&
    __CPROVER_r_ok(sub->pvPublishCallbackContext, CALLBACK_CONTEXT_LENGTH);
}

/****************************************************************
 * MQTTContext_t
 ****************************************************************/

// do the right thing!

Link_t *newTxBufferList(Link_t *head, size_t size) {
  if (!head)
    head = malloc(sizeof(Link_t));
  listINIT_HEAD(head);
  //for (int i = 0; i < size; i++)
  // use switch statement
  listADD(head, &mqttbufferGET_LINK(newMqttBuffer(NULL)));
  listADD(head, &mqttbufferGET_LINK(newMqttBuffer(NULL)));
  return head;
}

MQTTContext_t *newMQTTContext(MQTTContext_t *context) {
  if (!context)
    context = can_fail_malloc(sizeof(MQTTContext_t));

  if (context) {
    context->pxCallback = nullCallback;
    context->pvCallbackContext = malloc(CALLBACK_CONTEXT_LENGTH);
    // magic number to test context really used?

    // add nonnull checks to is valid checks.

    /* receive buffer containing the message being parsed */
    context->xRxBuffer = newMqttBuffer(NULL);

    // put in is valid
    // this comes from the specification
    __CPROVER_assume(1 <= context->xRxMessageState.ucRemaingingLengthFieldBytes);
    __CPROVER_assume(context->xRxMessageState.ucRemaingingLengthFieldBytes <= 4);

    /* transmit buffers containing messages waiting for ack */
    newTxBufferList(&(context->xTxBufferListHead), 2);

    // malloc sizeof(*(context->pvSendContext))
    context->pvSendContext = malloc(sizeof(UBaseType_t));
    context->pxMQTTSendFxn = malloc(sizeof(MQTTSend_t));
    //context->pxCallback = malloc(sizeof(MQTTEventCallback_t));

    context->xBufferPoolInterface.pxGetBufferFxn =
      malloc(sizeof(MQTTGetFreeBuffer_t));
    context->xBufferPoolInterface.pxReturnBufferFxn =
      malloc(sizeof(MQTTReturnBuffer_t));
  }

  return(context);

}
