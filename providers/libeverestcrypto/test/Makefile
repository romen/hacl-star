include ../../../../Makefile.include

test.exe:
	gcc-7 -c test.c -o test.o \
		-I .. -I ../c -I ../../libhacl -I ../../libvale -I $(OPENSSL_HOME)/include
	gcc-7 test.o ../libeverestcrypto.a -L .. \
		-I .. -I ../c -I ../../libhacl -I ../../libvale -I $(OPENSSL_HOME)/include \
		-o test.exe

clean:
	rm -rf *~ *.exe *.o
