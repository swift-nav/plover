- integer conversion rules just like in C
- shape (gets vector of dimensions)
- math operators from cmath.h
- reshaping of vectors
- vertical and horizontal concat.  should be able to concat along any dimension:
  x # y =  vec i in 0:(n+m) -> if i < n then x[i] else y[i-n]  -- "horizontal"
  x & y =  vec i in 0:_ -> vec j in 0:(n+m) -> if i < n then x[i,j] else y[i,j-n] -- "vertical"
- multidimensional transpose?
  x^T = vec i_1 in _ -> vec i_2 in _ -> ... vec i_d in _ -> x[i_d,...,i_1]

  but... x^T for a 1-d vector remains a 1-d vector, so outer product
  x^T * y does not work.

  but... maybe vec(x) * y is the correct way to write this (since then
  first vector becomes row vector)
- REPL (and associated intepreter)
- fix struct representation.  right now structs are always pointers,
  so an array of structs becomes a double pointer.  this is incorrect.


- external/internal function names
- typedefs referring to types other than structs
- f (x,y,...) === f x y ...


- Implement:
  - dgelsy - Least squares using QR
  - dgeqp3 - QR fact.
  - dgetrf - LU fact.
  - dgetrs - Linear system solver using LU
  - dorgqr - Q from QR?
  - dpotrf - Cholesky fact. of real symmetric
  - dpotri - inverse of real symm. pos. def.
  - dtrtri - inverse of triangular
  - lsame - char comparison
