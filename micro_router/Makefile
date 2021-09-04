TAS_CODE?= ${HOME}/tas/
RTE_SDK ?= $(HOME)/dpdk/x86_64-native-linuxapp-gcc
DPDK_PMDS ?= ixgbe i40e tap virtio

CPPFLAGS+= -I$(TAS_CODE)/include
CFLAGS = -std=gnu99 -g -Wall -O3 -march=native
LDFLAGS =-m64 -g -O3 -pthread  -march=native -no-pie

CPPFLAGS+= -I$(RTE_SDK)/include -I$(RTE_SDK)/include/dpdk
LDFLAGS+= -L$(RTE_SDK)/lib/
LDLIBS+= -Wl,--whole-archive \
	$(addprefix -lrte_pmd_,$(DPDK_PMDS)) \
	-lrte_eal -lrte_mempool -lrte_mempool_ring -lrte_hash \
	-lrte_ring -lrte_kvargs -lrte_ethdev -lrte_mbuf \
	-lnuma -lrte_bus_pci -lrte_pci \
	-lrte_net -lrte_bus_vdev \
	-lrte_gso  \
	-Wl,--no-whole-archive

LDLIBS+= -lm -lpthread -lrt -ldl

all: router

router: router.o $(TAS_CODE)/lib/utils/rng.o $(TAS_CODE)/lib/utils/utils.o
	$(CC) $(LDFLAGS) -o $@ $^ $(LDLIBS)

clean:
	rm -f *.o router

.PHONY: all clean
