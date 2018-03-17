include ../Makefile.include

.PHONY: libhacl libvale

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

libeverestcrypto: libhacl libvale
	mkdir -p libeverestcrypto/build
	cp libhacl/libhacl.a libeverestcrypto/build
	cp libvale/libvale.a libeverestcrypto/build
	$(CC) -c libeverestcrypto/c/Everest_Crypto_Full.c -I libhacl -I libvale/c -I $(KREMLIN_HOME)/kremlib \
		-o libeverestcrypto/build/Everest_Crypto_Full.o
	cd libeverestcrypto/build && \
	gar -x libhacl.a && \
	gar -x libvale.a && \
	gar -qc libeverest.a  *.o
	cp libeverestcrypto/build/libeverest.a libeverestcrypto
	rm -rf libeverestcrypto/build

clean:
	$(MAKE) clean -C libvale
	rm -rf *~ libeverestcrypto/*.a
