from prelude cimport s32

cdef extern from "main.c":
    double test (const s32 n, double * m, double * x);
