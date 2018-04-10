include ../../../Makefile.include

all: test.exe

test.exe:
	$(CC) -c test.c -o test.o \
		-I .. -I ../c -I ../../libhacl -I ../../libvale -I $(OPENSSL_HOME)/include
	$(CC) test.o -L . -leverestcrypto -o test.exe

clean:
	rm -rf *~ *.exe *.o *.so *.a *.dylib
