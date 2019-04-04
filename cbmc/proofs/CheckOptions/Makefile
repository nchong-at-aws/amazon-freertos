################################################################
# CheckOptions
#
# The proof depends on no parameters: all loops are independent of
# buffer sizes.
#
# The proof depends on a simple refactoring of the code: The loop bodies
# of two nested inner and outer loops are extracted into inner and outer
# functions (a manual implementation of loop invariants).  The inner
# function (loop body), then the outer function (loop body), then the
# CheckOptions function itself are independently specified and verified,
# with specifications of nested functions used in the verification of
# the enclosing function).  The proof is driven by
# Makefile-CheckOptions, Makefile-CheckOptionsOuter,
# Makefile-CheckOptionsInner.
#
ENTRY=CheckOptions

BUFFER_SIZE = 100

OBJS = \
  $(ENTRY)_harness.goto \
  $(FREERTOS)/lib/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_IP.goto \
  $(FREERTOS)/lib/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_WIN.goto \
  $(FREERTOS)/lib/FreeRTOS-Plus-TCP/source/FreeRTOS_Stream_Buffer.goto \
  $(FREERTOS)/lib/FreeRTOS/tasks.goto \
  $(FREERTOS)/lib/FreeRTOS/list.goto \
  # empty

H_DEF = \
  -DBUFFER_SIZE=$(BUFFER_SIZE) \
  # empty

H_CBMCFLAGS = \
  --unwind 1 \
  --unwindset prvCheckOptions.0:41 \
  # empty

include ../Makefile.$(OS)
include ../Makefile.project
