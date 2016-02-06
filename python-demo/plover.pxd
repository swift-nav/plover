from prelude cimport s32

cdef extern from "main.c":
    double test (const s32 n, double * m, double * x);
    void kp (const s32 dim, const double * x, const double * P, const double * F, const double * Q, double * x_new, double * P_new);
