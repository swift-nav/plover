all: cython

cython: libplover.a libqr.a libprelude.a setup.py plover.pyx plover.pxd prelude.pxd
	export LDFLAGS="-L." && \
	python setup.py build_ext -i -v

libplover.a: main.o
	ar rcs libplover.a main.o

libprelude.a: prelude.o
	ar rcs libprelude.a prelude.o

libqr.a: qr.o
	ar rcs libqr.a qr.o

prelude.o main.o qr.o : main.plv
	plover -I ../examples ../examples/prelude.plv ../examples/qr.plv main.plv && \
	gcc -fpic -c -o main.o  main.c && \
	gcc -fpic -c -o qr.o  qr.c && \
	gcc -fpic -c -o prelude.o  prelude.c

.PHONY: clean
clean:
	rm -rf build/ *.o *.a main.c prelude.c qr.c main.h prelude.h qr.h plover.so plover.c
