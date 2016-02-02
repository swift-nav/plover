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
