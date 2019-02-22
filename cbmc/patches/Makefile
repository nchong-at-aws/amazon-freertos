BRANCH=freertos

default:
	git format-patch $(BRANCH)..$(BRANCH)-cbmc-patches

patch:
	for p in *.patch; do (cd ../..; patch -p1 < cbmc/patches/$${p}) done

unpatch:
	git checkout ../../lib

#patching file lib/FreeRTOS-Plus-TCP/include/FreeRTOS_IP_Private.h
#patching file lib/include/private/list.h
#patching file lib/FreeRTOS-Plus-TCP/source/FreeRTOS_DHCP.c
#patching file lib/FreeRTOS-Plus-TCP/source/FreeRTOS_DNS.c
#patching file lib/FreeRTOS-Plus-TCP/source/FreeRTOS_TCP_WIN.c
