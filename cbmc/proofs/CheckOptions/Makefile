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

UNWIND_GOTO=0
BUFFER_SIZE = 100
UNWINDING = --unwind $(UNWIND) --unwindset prvCheckOptions.0:41 --unwinding-assertions

OBJS = \
  CheckOptions_harness.goto \
  $(FREERTOS)/lib/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_IP.goto \
  $(FREERTOS)/lib/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_WIN.goto \
  $(FREERTOS)/lib/FreeRTOS-Plus-TCP/source/FreeRTOS_Stream_Buffer.goto \
  $(FREERTOS)/lib/FreeRTOS/tasks.goto \
  $(FREERTOS)/lib/FreeRTOS/list.goto

H_DEF = -DBUFFER_SIZE=$(BUFFER_SIZE)

CheckOptions_compiled.goto: CheckOptions_harness.c
	$(GOTO_CC) $(O_COMPILE_ONLY) $@ $(INC) $(CFLAGS) $<

CheckOptions_linked.goto: $(OBJS)
	$(GOTO_CC) $(O_COMPILE_LINK) $@ --function harness $(OBJS)

CheckOptions_library.goto: CheckOptions_linked.goto
	 $(GOTO_INSTRUMENT) --add-library $< $@ \
		> CheckOptions_library.txt 2>&1

CheckOptions_drop.goto: CheckOptions_library.goto
	$(GOTO_INSTRUMENT) --drop-unused-functions $< $@ \
		> CheckOptions_drop.txt 2>&1

CheckOptions_slice.goto: CheckOptions_drop.goto
	$(GOTO_INSTRUMENT) --slice-global-inits $< $@ \
		> CheckOptions_slice.txt 2>&1

CheckOptions.goto: CheckOptions_slice.goto
	cp $< $@

include ../Makefile.dumb
