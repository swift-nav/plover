all: cython

cython: libplover.a libprelude.a setup.py plover.pyx plover.pxd prelude.pxd
	export LDFLAGS="-L." && \
	python setup.py build_ext -i -v

libplover.a: main.o
	ar rcs libplover.a main.o

libprelude.a: prelude.o
	ar rcs libprelude.a prelude.o

prelude.o main.o : main.plv
	plover -I ../examples ../examples/prelude.plv main.plv && \
	gcc -fpic -c -o main.o  main.c && \
	gcc -fpic -c -o prelude.o  prelude.c

.PHONY: clean
clean:
	rm -rf build/ *.o *.a main.c prelude.c main.h prelude.h plover.so plover.c
