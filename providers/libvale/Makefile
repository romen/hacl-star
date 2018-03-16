include ../../Makefile.include

# Override to get cross-compilation
MARCH?=$(shell uname -m)

UNAME6=$(shell uname | cut -c 1-6)
SED=$(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)

ifeq ($(UNAME6),CYGWIN)
  CC=$(MARCH)-w64-mingw32-gcc
  AR=x86_64-w64-mingw32-ar
else ifeq ($(MARCH),i686)
  CC=gcc -m32
  AR=ar
else
  CC=gcc
  AR=ar
endif

ifeq ($(UNAME),Darwin)
  VARIANT=-Darwin
else ifeq ($(UNAME),Linux)
  VARIANT=-Linux
endif

ifeq ($(OS),Windows_NT)
  FPIC =
else
  ifeq ($(UNAME),Darwin)
    FPIC =
  else
    FPIC =-fPIC
  endif
endif


VALE_HOME ?= ../../../../vale
KREMLIN_HOME ?= ../../../../kremlin
CCOPTS=$(FPIC) -Wall -Wextra -Werror -I $(KREMLIN_HOME)/kremlib
CC:=$(CC) $(CCOPTS)


all: libvale.a

ALL_OBJ= asm/sha256-$(MARCH)$(VARIANT).o c/sha256_main_i.o c/Vale_Hash_SHA2_256.o \
	asm/aes-$(MARCH)$(VARIANT).o c/Vale_AES.o

libvale.a: $(ALL_OBJ)
	ar -cr $@ $^

%.o: %.S
	$(CC) -c $< -o $@

%.o: %.c
	$(CC) -c $< -o $@


.PHONY: import
import:
	@if [ x"$(VALE_HOME)" = x ]; then echo "VALE_HOME not defined"; exit 1; fi
	rm -rf asm/
	cp $(VALE_HOME)/obj/aes-gcc.S asm/aes-x86_64.S
	cp $(VALE_HOME)/obj/sha256-gcc.S asm/sha256-x86_64.S
	cp $(VALE_HOME)/obj/aes-macos.S asm/aes-x86_64-Darwin.S
	cp $(VALE_HOME)/obj/sha256-macos.S asm/sha256-x86_64-Darwin.S
	cp $(VALE_HOME)/obj/aes-linux.S asm/aes-x86_64-Linux.S
	cp $(VALE_HOME)/obj/sha256-linux.S asm/sha256-x86_64-Linux.S
	$(SED) -i 's/.section .text/.text/' *.S
	for f in $(VALE_OBJ_FILES); do cp $(VALE_HOME)/obj/crypto/hashing/$$f .; done
	for f in $(VALE_UTIL_FILES); do cp $(VALE_HOME)/src/lib/util/$$f .; done

clean:
	rm -f *.a *.o *~
	rm -f c/*.o c/*~
	rm -f asm/*.o asm/*~
