.PHONY: libvale

all: libeverest

HACL_HEADERS= $(addprefix $(HACL_HOME)/snapshots/hacl-c/, \
	Hacl_Chacha20.h \
	Hacl_Chacha20_Vec128.h \
	Hacl_Curve25519.h \
	Hacl_Ed25519.h \
	Hacl_HMAC_SHA2_256.h \
	Hacl_Salsa20.h \
	Hacl_SHA2_256.h \
	Hacl_SHA2_384.h \
	Hacl_SHA2_512.h \
	Hacl_Policies.h \
	Hacl_Poly1305_32.h \
	Hacl_Poly1305_64.h)

libhacl:
	mkdir -p libhacl
	cp $(HACL_HOME)/code/api/HACL.fsti libhacl/
	cp $(HACL_HEADERS) libhacl/
	cp $(HACL_HOME)/snapshots/api/HACL.h libhacl/
	$(MAKE) -C $(HACL_HOME) build
	cp $(HACL_HOME)/build/libhacl* libhacl

libvale:
	$(MAKE) -C libvale

libeverest: libhacl libvale
	mkdir -p everest_crypto/build
	cp libhacl/libhacl.a everest_crypto/build
	cp libvale/vale.a everest_crypto/build/libvale.a
	cd everest_crypto/build && \
	gar -x libhacl.a && \
	gar -x libvale.a && \
	gar -qc libeverest.a  *.o
	cp everest_crypto/build/libeverest.a everest_crypto
	rm -rf everest_crypto/build

clean:
	$(MAKE) clean -C libvale
	rm -rf *~ everest_crypto/*.a
