cimport plover
import numpy as np
cimport numpy as np
from libc.stdlib cimport malloc, free

# example wrapper
def wrapper(np.ndarray[double, ndim=1, mode="c"] nparr):
    n = len(nparr)
    cdef np.ndarray[double, ndim=2, mode="c"] npmat = np.zeros([n, n])
    out = plover.test(n, &npmat[0,0], &nparr[0])
    return (out, npmat, nparr)

def kalman_predict(
        np.ndarray[double, ndim=1, mode="c"] x,
        np.ndarray[double, ndim=2, mode="c"] P,
        np.ndarray[double, ndim=2, mode="c"] F,
        np.ndarray[double, ndim=2, mode="c"] Q):
    dim = len(x)
    cdef np.ndarray[double, ndim=1, mode="c"] x_new = np.zeros([dim])
    cdef np.ndarray[double, ndim=2, mode="c"] P_new = np.zeros([dim, dim])
    plover.kalman_predict_(dim, &x[0], &P[0,0], &F[0,0], &Q[0,0], &x_new[0], &P_new[0,0])
    return (x_new, P_new)

def kalman_update(
        np.ndarray[double, ndim=1, mode="c"] x,
        np.ndarray[double, ndim=2, mode="c"] P,
        np.ndarray[double, ndim=1, mode="c"] y,
        np.ndarray[double, ndim=2, mode="c"] H,
        np.ndarray[double, ndim=2, mode="c"] R):
    xdim = len(x)
    dim = len(y)
    cdef np.ndarray[double, ndim=1, mode="c"] x_new = np.zeros([xdim])
    cdef np.ndarray[double, ndim=2, mode="c"] P_new = np.zeros([xdim, xdim])
    plover.kalman_update_(xdim, dim, &x[0], &P[0,0], &y[0], &H[0,0], &R[0,0], &x_new[0], &P_new[0,0])
    return (x_new, P_new)

def inverse(np.ndarray[double, ndim=2, mode="c"] P):
    dim = len(P)
    cdef np.ndarray[double, ndim=2, mode="c"] new = np.zeros([dim, dim])
    plover.matrix_inverse(dim, &P[0,0], &new[0,0])
    return new

def print_all(
        np.ndarray[double, ndim=1, mode="c"] innovation,
        np.ndarray[double, ndim=2, mode="c"] S,
        np.ndarray[double, ndim=2, mode="c"] Si,
        np.ndarray[double, ndim=2, mode="c"] K,
        np.ndarray[double, ndim=1, mode="c"] x_new,
        np.ndarray[double, ndim=2, mode="c"] P_new):
    dim = len(innovation)
    plover.print_all_(dim, &innovation[0], &S[0,0], &Si[0,0], &K[0,0], &x_new[0], &P_new[0,0])
