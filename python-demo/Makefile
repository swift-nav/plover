all: cython main

MAIN_SRC = $(wildcard *.plv)

cython: libplover_main.a libqr.a libprelude.a libfilter.a liboperations.a libutil.a \
	      setup.py plover.pyx plover.pxd prelude.pxd
	export LDFLAGS="-L." && \
	python setup.py build_ext -i -v

lib%.a : %.o
	ar rcs $@ $<

%.o : %.c
	gcc -fpic -c $<

plover_main.c prelude.c qr.c: ../examples/prelude.plv $(MAIN_SRC)
	plover -I ../examples ../examples/prelude.plv ../examples/qr.plv util.plv operations.plv filter.plv plover_main.plv

.PHONY: clean
clean:
	rm -rf build/ *.o *.a plover_main.c prelude.c qr.c plover_main.h prelude.h qr.h plover.so plover.c

# TODO: pattern for c files
main: plover_main.c
	gcc -o test_suite plover_main.c prelude.c qr.c util.c filter.c operations.c rand.c
