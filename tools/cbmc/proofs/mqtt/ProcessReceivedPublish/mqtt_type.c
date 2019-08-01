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

struct MqttBuffer *allocate_MqttBuffer(struct MqttBuffer *buffer) {
  if (buffer == NULL)
    buffer = malloc(sizeof(struct MqttBuffer));

  if (buffer) {
    // these assignments cannot be moved to the validation function
    // prev and next need to be defined here so list operations work
    buffer->Metadata.xLink.pxPrev = &(buffer->Metadata.xLink);
    buffer->Metadata.xLink.pxNext = &(buffer->Metadata.xLink);

    // to is valid
    /* should make this arbitrary sizeof(metadata) + 0 to 100 */
//    buffer->Metadata.ulBufferLength = sizeof(struct MqttBuffer);
    /* should make this arbitrary 0 to 100 within effective buffer length */
//    buffer->Metadata.ulDataLength =
//      sizeof(struct MqttBuffer) - sizeof(MQTTBufferMetadata_t);
  }

  return buffer;
}

int is_valid_MqttBuffer(struct MqttBuffer *buffer) {
  int b = 1;

  b = b && buffer;

  // buffer is readable
  b = b && __CPROVER_r_ok(buffer, sizeof(struct MqttBuffer));
  b = b && __CPROVER_r_ok(buffer->data, MQTT_BUFFER_USER_DATA_LENGTH);

  // buffer comes from a doubly linked buffer pool
  b = b && __CPROVER_r_ok(buffer->Metadata.xLink.pxPrev, sizeof(Link_t));
  b = b && __CPROVER_r_ok(buffer->Metadata.xLink.pxNext, sizeof(Link_t));

  b = b && buffer->Metadata.ulBufferLength <= sizeof(struct MqttBuffer);
  b = b && buffer->Metadata.ulDataLength <=
    sizeof(struct MqttBuffer) - sizeof(MQTTBufferMetadata_t);

  return b;
}

/****************************************************************
 * MQTTSubscription_t
 ****************************************************************/

MQTTSubscription_t *
allocate_MQTTSubscription(MQTTSubscription_t *sub) {
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
 * MQTTSubscriptionManager
 ****************************************************************/

MQTTSubscriptionManager_t *
allocate_MQTTSubscriptionManager(MQTTSubscriptionManager_t *mgr) {
  if (!mgr)
    mgr = can_fail_malloc(sizeof(MQTTSubscriptionManager_t));

  if (mgr) {
    for (int i=0; i < mqttconfigSUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS; i++)
      allocate_MQTTSubscription(&mgr->xSubscriptions[i]);
  }

  return mgr;
}

int is_valid_MQTTSubscriptionManager(MQTTSubscriptionManager_t *mgr) {
  if (!mgr) return 0;

  if (mgr->ulInUseSubscriptions >
      mqttconfigSUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS) return 0;

  for (int i=0; i < mgr->ulInUseSubscriptions; i++)
    if (!is_valid_MQTTSubscription(&mgr->xSubscriptions[i])) return 0;

  return 1;
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

  struct MqttBuffer *buf1 = allocate_MqttBuffer(NULL);
  struct MqttBuffer *buf2 = allocate_MqttBuffer(NULL);
  __CPROVER_assume(buf1);
  __CPROVER_assume(buf2);
  listADD(head, &mqttbufferGET_LINK(buf1));
  listADD(head, &mqttbufferGET_LINK(buf2));
  return head;
}

MQTTContext_t *allocate_MQTTContext(MQTTContext_t *context) {
  if (!context)
    context = can_fail_malloc(sizeof(MQTTContext_t));

  if (context) {
    context->pxCallback = nullCallback;
    context->pvCallbackContext = malloc(CALLBACK_CONTEXT_LENGTH);
    // magic number to test context really used?

    /* receive buffer containing the message being parsed */
    context->xRxBuffer = allocate_MqttBuffer(NULL);

    /* transmit buffers containing messages waiting for ack */
    newTxBufferList(&(context->xTxBufferListHead), 2);

    allocate_MQTTSubscriptionManager(&context->xSubscriptionManager);

    // malloc sizeof(*(context->pvSendContext))
    context->pvSendContext = malloc(sizeof(UBaseType_t));
    context->pxMQTTSendFxn = malloc(sizeof(MQTTSend_t));
    //context->pxCallback = malloc(sizeof(MQTTEventCallback_t));

    context->xBufferPoolInterface.pxGetBufferFxn =
      malloc(sizeof(MQTTGetFreeBuffer_t));
    context->xBufferPoolInterface.pxReturnBufferFxn =
      malloc(sizeof(MQTTReturnBuffer_t));
  }

  return context;
}


int is_valid_MQTTContext(MQTTContext_t *context) {
  int b = 1;

  b = b && context;
  b = b && context->pxCallback;
  b = b && context->pvCallbackContext;
  b = b && __CPROVER_r_ok(context->pvCallbackContext, CALLBACK_CONTEXT_LENGTH);
  b = b && is_valid_MqttBuffer(context->xRxBuffer);

  //t his comes from the specification
  b = b && 1 <= context->xRxMessageState.ucRemaingingLengthFieldBytes;
  b = b && context->xRxMessageState.ucRemaingingLengthFieldBytes <= 4;

  b = b && is_valid_MQTTSubscriptionManager(&context->xSubscriptionManager);

  return b;
}
