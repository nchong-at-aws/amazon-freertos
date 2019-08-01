#pragma once

#include "aws_mqtt_lib.h"

MQTTContext_t *allocate_MQTTContext(MQTTContext_t *context);


int is_valid_MQTTContext(MQTTContext_t *context);
int is_valid_MqttBuffer(struct MqttBuffer *buffer);
