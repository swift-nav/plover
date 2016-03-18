To modify this subproject:
 - add new code to `main.plv`. run `make` to generate header file `main.h`
 - add new signature to `plover.pxd` to match that in `main.h`
 - add wrapper function to `plover.pyx`. see examples there for guidance.
 - successfully run make to build `plover.so`
 - copy `plover.so` to desired location
 - in python, use `import plover` as you would with any other library.
