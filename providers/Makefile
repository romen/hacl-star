include ../Makefile.include

.PHONY: libhacl libvale

all: libeverestcrypto

# TODO: Reuse a target by importing Makefile.build instead
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

# This target builds the libhacl static library from an
# up-to-date version of the HACL* snapshot and imports the
# associated HACL.fsti, HACL.h and necessary header files.
libhacl:
	mkdir -p libhacl
	$(MAKE) build -C $(HACL_HOME) # Top-level HACL* target
	cp $(HACL_HOME)/build/libhacl* libhacl
	cp $(HACL_HOME)/code/api/HACL.fsti libhacl/
	cp $(HACL_HOME)/snapshots/api/HACL.h libhacl/
	cp $(HACL_HEADERS) libhacl/

# This target builds a libvale static library from a locally
# stored version of Vale and provides a Vale.fsti and Vale.h.
# TODO: Make sure to always import the most recent version
# of Vale as it is what happens for HACL*.
libvale:
	$(MAKE) -C libvale

# This target builds the libeverestcrypto static library by
# unpacking and repacking together libhacl.a, libvale.a and
# libcrypto.a. It provides an Everest_Crypto.fsti and an
# Everest_Crypto.h associated to that library as well.
libeverestcrypto: libhacl libvale
	mkdir -p libeverestcrypto/build
	cp libhacl/libhacl.a libeverestcrypto/build
	cp libvale/libvale.a libeverestcrypto/build
	cp $(BORINGSSL_HOME)/build/crypto/libcrypto.a libeverestcrypto/build
	$(CC) -c libeverestcrypto/c/Everest_Crypto_Full.c \
		-I libhacl -I libvale/c -I $(KREMLIN_HOME)/kremlib -I $(BORINGSSL_HOME)/include \
		-o libeverestcrypto/build/Everest_Crypto_Full.o
	cd libeverestcrypto/build && \
	gar -x libhacl.a && \
	gar -x libvale.a && \
	gar -x libcrypto.a && \
	gar -rcs libeverestcrypto.a *.o
#	glibtool --mode=link --tag=CC gar --target=mach-o-x86-64 -o libeverestcrypto.a -static libhacl.a libvale.a libcrypto.a
	cp libeverestcrypto/build/libeverestcrypto.a libeverestcrypto
	rm -rf libeverestcrypto/build
	@echo $(CYAN)"# Done ! Generated libraries can be found in: "$(NORMAL)
	@echo $(CYAN)"# 'libhacl/' for the HACL* crypto provider"$(NORMAL)
	@echo $(CYAN)"# 'libvale/' for the Vale crypto provider"$(NORMAL)
	@echo $(CYAN)"# 'libeverestcrypto/' for the Everest_Crypto provider"$(NORMAL)


clean:
	$(MAKE) clean -C libvale
	rm -rf *~ libeverestcrypto/*.a libeverestcrypto/*.o
	rm -rf *~ libeverestcrypto/build
