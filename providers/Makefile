all: libhacl-refresh

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

libhacl-refresh:
	mkdir -p libhacl
	cp $(HACL_HOME)/code/api/HACL.fsti libhacl/
	# $(MAKE) -C $(HACL_HOME) snapshots/hacl-c
	cp $(HACL_HEADERS) libhacl/
	cp $(HACL_HOME)/snapshots/api/HACL.h libhacl/
	$(MAKE) -C $(HACL_HOME) build
	cp $(HACL_HOME)/build/libhacl* libhacl
