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
        np.ndarray[double, ndim=2, mode="c"] Q,
        ):
    dim = len(x)
    cdef np.ndarray[double, ndim=1, mode="c"] x_new = np.zeros([dim])
    cdef np.ndarray[double, ndim=2, mode="c"] P_new = np.zeros([dim, dim])
    plover.kp(dim, &x[0], &P[0,0], &F[0,0], &Q[0,0], &x_new[0], &P_new[0,0])
    return (x_new, P_new)
