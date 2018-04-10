include ../Makefile.include

.PHONY:

all: libevercrypt/libevercrypt.so

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
libhacl/libhacl.a:
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
libvale/libvale.a:
	$(MAKE) -C libvale

# This target builds the libevercrypt static library by
# unpacking and repacking together libhacl.a, libvale.a and
# libcrypto.a. It provides an Everest_Crypto.fsti and an
# Everest_Crypto.h associated to that library as well.
libevercrypt/libevercrypt.so: libhacl/libhacl.a libvale/libvale.a
	mkdir -p libevercrypt/build
	cp libhacl/libhacl.a libevercrypt/build
	cp libvale/libvale.a libevercrypt/build
	cp $(BORINGSSL_HOME)/build/crypto/libcrypto.a libevercrypt/build
	cd libevercrypt/c && \
	$(CC) -c Everest_Crypto_Full.c \
		-I ../../libhacl -I ../../libvale/c -I $(KREMLIN_HOME)/kremlib -I $(BORINGSSL_HOME)/include \
		-o Everest_Crypto_Full.o
	cp libevercrypt/c/Everest_Crypto_Full.o libevercrypt/build
	cd libevercrypt/build && \
	$(CC) -shared Everest_Crypto_Full.o libhacl.a libvale.a libcrypto.a -o libevercrypt.so
	cp libevercrypt/build/libevercrypt.so libevercrypt/libevercrypt.so
	rm -rf libevercrypt/build
	@echo $(CYAN)"# Done ! Generated libraries can be found in: "$(NORMAL)
	@echo $(CYAN)"# 'libhacl/' for the HACL* crypto provider"$(NORMAL)
	@echo $(CYAN)"# 'libvale/' for the Vale crypto provider"$(NORMAL)
	@echo $(CYAN)"# 'libevercrypt/' for the Everest_Crypto provider"$(NORMAL)

test: libevercrypt/libevercrypt.so
	cp libevercrypt/libevercrypt.so libevercrypt/test
	$(MAKE) test.exe -C libevercrypt/test
	cd libevercrypt/test && ./test.exe

clean:
	rm -rf *.{~,o,a,so,dylib,exe}
	rm -rf libhacl/*.{~,o,a,so,dylib,exe}
	$(MAKE) clean -C libvale
	$(MAKE) clean -C libevercrypt/test
	rm -rf *~ libevercrypt/*.{o,a,so,dylib,exe}
	rm -rf *~ libevercrypt/c/*.o
	rm -rf *~ libevercrypt/build
