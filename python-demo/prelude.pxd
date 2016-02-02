cimport libc.math
cimport libc.stdlib
cimport libc.float
cimport libc.stdint
cdef extern from "prelude.c":

    ctypedef libc.stdint.int8_t s8;
    ctypedef libc.stdint.int16_t s16;
    ctypedef libc.stdint.int32_t s32;
    ctypedef libc.stdint.int64_t s64;
    ctypedef libc.stdint.uint8_t u8;
    ctypedef libc.stdint.uint16_t u16;
    ctypedef libc.stdint.uint32_t u32;
    ctypedef libc.stdint.uint64_t u64;
