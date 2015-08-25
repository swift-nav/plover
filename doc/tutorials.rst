==================
 Plover Tutorials
==================

:Authors:  Scott Kovach, Kyle Miller
:Modified: August 2015

This part of the documentation gives worked examples of using Plover.

.. contents:: Table of Contents

Matrix Multiplications
======================

A quick application of using Plover is to create bespoke functions
which operate on matrices.  A very basic example is a matrix times a
vector:
::

   mul_mat_vec {m,n} (A :: double[m,n]) (v :: double[n]) :: double[m]
     := A * v;

This function takes two implicit arguments (``m`` and ``n``) which
give the dimensions of the :math:`m\times n` matrix ``A`` and an
:math:`n`-dimensional vector ``v``.  Putting this into a file called
``mats.plv``, we compile it with Plover using
::

   $ plover mats.plv

which creates two files, ``mats.c`` and ``mats.h``.  The resulting C
definition is
::

   void mul_mat_vec (const s32 m, const s32 n,
                     const double * A, const double * v,
                     double * result)
   {
       for (s32 idx = 0; idx < m; idx++) {
           double sum = 0;

           for (s32 idx2 = 0; idx2 < n; idx2++) {
               sum += A[n * idx + idx2] * v[idx2];
           }
           result[idx] = sum;
       }
   }

with a corresponding definition in the header file.  The rules for
creating the C function type from a Plover type are simple: the
parameters for the C function appear in the same order as they appear
in the Plover definition, and if the result is a vector type (i.e.,
non-scalar), it is appended as the last argument.  The caller is
responsible for allocating the memory of the returned vector.

Another example is computing a quadratic form  :math:`v^TAv`:
::

   mat_quad_form {n} (A :: double[n,n]) (v :: double[n]) :: double
     := (v^T * A * v)[0];

Multiplication is left-associative, so the inner expression is the
same as ``(v^T * A) * v``. The rule for taking the transpose of an
:math:`n`-dimensional vector is that it becomes a :math:`1\times
n`-dimensional matrix, and so the product with the :math:`n\times n`
matrix ``A``, giving a :math:`1\times n` matrix.  This is then
multiplied by the vector, and a matrix times a vector results in a
vector, in this case :math:`1`-dimensional.  This is indexed to get
the sole entry.  Alternatively, the body of the function could
equivalently be ``(A * v) * v``, without indexing, where the second
``*`` is a dot product between vectors.

Compiling this, the resulting C is
::

   double mat_quad_form (const s32 n,
                         const double * A, const double * v)
   {
       double sum = 0;

       for (s32 idx = 0; idx < n; idx++) {
           double sum2 = 0;

           for (s32 idx2 = 0; idx2 < n; idx2++) {
               sum2 += v[idx2] * A[n * idx2 + idx];
           }
           sum += sum2 * v[idx];
       }
       return sum;
   }

Notice that the Plover compiler does not generate the intermediate
matrix product.  This is because the later multiplication informs the
first that it will only be evaluating each element of the first at
most once, so the elements may be computed on demand.

Suppose that the vector were instead a matrix.  That is,
::

   mat_quad_prod {n,m} (A :: double[n,n]) (B :: double[n,m]) :: double[m,m]
     := B^T * A * B;

Plover generates the following code:
::

   void mat_quad_prod (const s32 n, const s32 m,
                       const double * A, const double * B,
                       double * result)
   {
       double tmp [m * n];

       for (s32 idx = 0; idx < m; idx++) {
           for (s32 idx2 = 0; idx2 < n; idx2++) {
               double sum = 0;

               for (s32 idx3 = 0; idx3 < n; idx3++) {
                   sum += B[m * idx3 + idx] * A[n * idx3 + idx2];
               }
               tmp[n * idx + idx2] = sum;
           }
       }
       for (s32 idx = 0; idx < m; idx++) {
           for (s32 idx2 = 0; idx2 < m; idx2++) {
               double sum = 0;

               for (s32 idx3 = 0; idx3 < n; idx3++) {
                   sum += tmp[n * idx + idx3] * B[m * idx3 + idx2];
               }
               result[m * idx + idx2] = sum;
           }
       }
   }

Since the second product will use the elements of the first product
multiple times, the compiler *memoizes* (or *spills*) the result onto
the stack.  If ``n`` is large relative to ``m`` this might be
unacceptable behavior on an embedded system, and we may be willing to
trade stack space for computation time.  Plover gives the ``nomemo``
operator to control whether a request to memoize an intermediate value
will be acknowledged.  This does not change the result of a
computation, but it might change whether the computation is computable
on a given system.  Concretely:
::

   mat_quad_prod_safe {n,m} (A :: double[n,n]) (B :: double[n,m]) :: double[m,m]
     := nomemo (B^T * A) * B;

gives
::

   void mat_quad_safe (const s32 n, const s32 m,
                       const double * A, const double * B,
                       double * result)
   {
       for (s32 idx = 0; idx < m; idx++) {
           for (s32 idx2 = 0; idx2 < m; idx2++) {
               double sum = 0;

               for (s32 idx3 = 0; idx3 < n; idx3++) {
                   double sum2 = 0;

                   for (s32 idx4 = 0; idx4 < n; idx4++) {
                       sum2 += B[m * idx4 + idx] * A[n * idx4 + idx3];
                   }
                   sum += sum2 * B[m * idx3 + idx2];
               }
               result[m * idx + idx2] = sum;
           }
       }
   }



Computing Correlation Vectors
=============================

The cross-correlation of two (real-valued) signals :math:`f` and
:math:`g` is defined to be

.. math::

   (f \star g)[i] = \sum_{j=-\infty}^\infty f[j] g[j+i]

For periodic signals with period :math:`N`, the bounds of the sum can
be restricted to having length :math:`N`, and, if we model :math:`f`
and :math:`g` as being vectors of length :math:`N`, this amounts to a
dot product of :math:`f` by a cyclic shift of :math:`g`.

In Plover, the right-hand side can be written as ``f * (g[i:] #
g[:i])``.  The ``*`` operator computes the dot product when given
vector operands, and the ``#`` operator concatenates two vectors.
Like in Python or Matlab, vectors can be *sliced* by indexing them
with a range of values.  The lower- or upper- bounds may be omitted on
the range operator ``:``, and they default to the bounds of the sliced
vector.  Here, ``i:`` and ``:i`` are equivalent to the vectors
``vec(i,i+1,...,N-1)`` and ``vec(0,1,...,i-1)``, respectively.

With this, we can make a function which computes all of the
cross-correlations of two vectors of length ``N``:
::

   cross_cor {N} (f :: double[N]) (g :: double[N]) :: double[N] :=
     vec i in N -> f * (g[i:] # g[:i]);

The declaration for the function gives ``N`` as an implicit parameter,
``f`` and ``g`` as vectors of length ``N`` with double-precision
floating-point numbers as values, and a return type which is also a
vector of length ``N`` with doubles as values.

The body of the function is given after the ``:=`` definition
operator.  The body creates a new vector of length ``N`` with ``i``
iterating over that range, computing the cross-correlation for each
offset ``i``.

.. note::
   The cross-correlation function can also be written as::

     cross_cor {N} (f :: double[N]) (g :: double[N]) :: double[N] :=
       vec i in N -> f * g[(i:i+N) % N];

   since arithmetic operators coerce their operands into vectors of
   compatible size and then vectorize the operation elementwise.


Auto-correlation is the cross-correlation of a vector with itself.
Given the above definition, we may write
::

   auto_cor {N} (f :: double[N]) :: double[N] :=
     cross_cor f f;

Since the first argument to ``cross_cor`` is implicit, Plover will try
to determine a valid argument to place there, which it will determine
using ``f`` and the return type for ``auto_cor``.  If we wish to be
explicit, we may instead write ``cross_cor {N} f f`` to pass the
implicit argument ``N``.

Putting these into a file called ``cor.plv``, we may compile them to C
by entering the directory and running ::

   $ plover cor.plv

This creates a files called ``cor.h`` and ``cor.c``, with ``cor.c``
containing the following definitions:
::

   void cross_cor (const s32 N, const double * f, const double * g, double * result)
   {
       for (s32 idx = 0; idx < N; idx++) {
           s32 i = idx;
           double sum = 0;

           for (s32 idx2 = 0; idx2 < N; idx2++) {
               double tmp;

               if (idx2 < -i + N) {
                   tmp = g[i + idx2];
               } else {
                   tmp = g[idx2 - (-i + N)];
               }
               sum += f[idx2] * tmp;
           }
           result[idx] = sum;
       }
   }
   void auto_cor (const s32 N, const double * f, double * result)
   {
       cross_cor(N, f, f, result);
   }

The auto-correlation of a random vector approximates a delta function
as the length of the vector goes to infinity.  We will make a test
which demonstrates this.

::

   import prelude;

   main () :: int :=
     ( v := normalize (vec i in 1000 -> rand_normal());
       print_vec $ auto_cor v;
       return 0;
     );

This imports the standard Plover library, and defines a ``main``
function.  The function creates a vector of 1000 random doubles,
normally distributed, and normalizes the vector so that its Euclidean
length is 1.  After this, the auto-correlation vector is printed.  In
Plover, the dollar sign acts like an open parenthesis which extends to
the end of an expression.

Compiling and running this file with::

  $ plover cor.plv
  $ gcc cor.c prelude.c -o cor
  $ ./cor

shows that the 0th element is ``1.0`` (since this entry represents the
dot product of the vector with itself), and the rest are relatively
small.  We can measure this with the following code:

::

   vec_mean {n} (v :: double[n]) :: double :=
     sum v / n;

   main () :: int :=
     ( w := vec N in 2:2000 -> (
              v := normalize $ vec i in N -> rand_normal();
              av := auto_corr v;
              vec_mean $ av[1:] .* av[1:]
            );
       print_vec w;
       return 0;
     );

The ``.*`` operator is the point-wise product ("Hadamard" product) and
effectively squares each element in the array.  So ``w`` is a vector
of the mean of the squares of the non-zero-offset auto-correlations
for various sizes of random vectors.  Plotting this vector in a
graphing application, one can see the errors decrease with the inverse
of the size of the vectors.

Programming a QR Least Squares Solver
=====================================

We're going to step through the implementation of a textbook algorithm: a QR
least squares solver for overdetermined systems. That is, given :math:`A\in
\R^{m\times n}` and :math:`b\in \R^m` with :math:`m \geq n`, we want to find a
vector :math:`x\in\R^n` such that the squared error :math:`\norm{Ax-b}` is
minimized. We give a brief explanation of the math first, following [MC2013]_.

Suppose we can compute an orthogonal matrix :math:`Q\in\R^{m\times m}` such
that

.. math::

  Q^T A = R = \begin{bmatrix}R_1 \\ 0 \end{bmatrix}
  \begin{matrix} \scriptstyle n \\ \scriptstyle m-n \end{matrix}

where :math:`R_1\in \R^{n\times n}` is upper triangular. Then we can write

.. math::

  Q^T b = \begin{bmatrix}c \\ d \end{bmatrix}
  \begin{matrix} \scriptstyle n \\ \scriptstyle m-n \end{matrix}

and we note that

.. math::

  \norm{Ax-b} = \norm{Q^TAx-Q^Tb} = \norm{R_1x-c}+\norm{d}

If :math:`A` is full rank, we can solve the system :math:`R_1x=c` exactly, and
the remaining error is :math:`d`.

The essential steps are:

1. Apply orthogonal transformations to :math:`A` and :math:`b` until
   :math:`A`'s first :math:`n` rows are upper triangular.
2. Backsolve the triangular system.
3. Return the solution and the error.

We will attempt to mindlessly follow the implementation given in [MC2013]_.

QR Factorization
----------------
First we apply a sequence of Givens rotations to introduce zeroes into our matrix :math:`A`.
A Givens rotation is a pair :math:`c=\cos(\theta)` and :math:`s=\sin(\theta)` such that

.. math::
  \begin{bmatrix}
    c & s \\
    -s & c
  \end{bmatrix}^T
  \begin{bmatrix}
  a \\ b
  \end{bmatrix}
  =
  \begin{bmatrix}
  r \\ 0
  \end{bmatrix}
  .

Pseudocode to calculate such a pair follows:

 | **givens** (a, b) **returns** [:math:`c, s`]
 | **if** :math:`b = 0`
 |   :math:`c = 1; s = 0`
 | **else if** :math:`\abs{b} > \abs{a}`
 |   :math:`\tau = -a/b; s = 1/\sqrt{1+\tau^2}; c = s\tau`
 | **else**
 |   :math:`\tau = -b/a; c = 1/\sqrt{1+\tau^2}; s = c\tau`

The plover version is below. We will step through it line by line.

::

  static givens (a :: double) (b :: double) :: double[2,2] := (
    c :: double;
    s :: double;
    if b == 0 then (
      c <- 1; s <- 0
    ) else if fabs b > fabs a then (
      tau := -a/b; s <- 1/sqrt(1+tau^2); c <- s*tau
    ) else (
      tau := -b/a; c <- 1/sqrt(1+tau^2); s <- c*tau;
    );

    mat( c, s ;
        -s, c );
  );

-------

::

  static givens (a :: double) (b :: double) :: double[2,2] := (
    ...
  );

Plover is statically typed, and all functions require a type
signature, although in many cases types can be inferred (see the
language reference section on type holes).  This function signature
indicates that the function ``givens`` is ``static`` (declared
``static`` in the generated ``C`` file, with no prototype in the
header file), takes two arguments ``a`` and ``b`` of type ``double``,
and returns a 2-by-2 matrix of doubles.  Function declarations and
variable initializations use the ``:=`` operator and must be
terminated by a semicolon.  Blocks are enclosed by parentheses, and
the expressions within a block are separated by semicolons.

::

    c :: double;
    s :: double;


A new local variable may either be declared with a type (``var ::
type;``) or with an initial value (``var :: optional_type :=
value;``), in which case the type is optional and can be inferred.  In
this case, ``c`` and ``s`` are set by each branch of the ``if``
expression below, so we declare them with only their types.  Declaring
a variable does not initialize it.

::

    if b == 0 then (
      c <- 1; s <- 0
    )

The condition of an ``if`` expression does not need enclosing
parentheses. The condition must be followed by the keyword ``then``
and an expression. In this case, we have a block which updates the
values of ``c`` and ``s``.  Updating variables must be done with
``<-`` .  An ``if`` should be terminated by a semicolon when used as a
statement.

.. note:: In Plover, everything is an expression.  Sometimes it is
          convenient to call an expression appearing in a block a
          *statement*.

::

    else if fabs b > fabs a then (
      tau := -a/b; s <- 1/sqrt(1+tau^2); c <- s*tau
    ) else (
      tau := -b/a; c <- 1/sqrt(1+tau^2); s <- c*tau
    );

``if`` statements are optionally followed by an ``else`` clause and
another expression or block. Here, the ``fabs`` function is called on
``b`` and on ``a``, and these values are compared to choose the branch.
The local ``tau`` is initialized, and ``c`` and ``s`` are updated as
shown in the pseudocode above.  The ``fabs`` and ``sqrt`` functions
are included in Plover's ``prelude`` module.

::

    mat( c, s ;
        -s, c );

The final expression in a block is treated as the value for that block. Here,
the function returns a 2-by-2 matrix literal containing the values we've just
computed. The output code below shows how this is translated into C.


Let's take a look at the C code generated so far:

::

  // excerpt, qr.c
  static void givens (const double a, const double b, double * result);
  void givens (const double a, const double b, double * result)
  {
      double c;
      double s;

      if (b == 0) {
          c = 1;
          s = 0;
      } else {
          if (fabs(a) < fabs(b)) {
              double tau;

              tau = -(a / b);
              s = 1 / sqrt(1 + tau * tau);
              c = s * tau;
          } else {
              double tau;

              tau = -(b / a);
              c = 1 / sqrt(1 + tau * tau);
              s = c * tau;
          }
      }
      result[2 * 0] = c;
      result[2 * 0 + 1] = s;
      result[2 * 1] = -s;
      result[2 * 1 + 1] = c;
  }

We can see that Plover passes the result matrix as an extra argument, and
stores the dense matrix in a flat array in row-major order. Arguments are by
default passed ``const``, but modifications are allowed with the ``out`` and
``inout`` parameter options; see the language reference. The rest of the code
matches the input closely.


Now we will use this routine to factor our matrix.  Starting at the lower left
corner, we go up and then right, introducing zeros with one Givens rotation at
a time. Pseudocode from [MC2013]_:


 | **qr_factor** (m, n, A)
 | **for** :math:`j = 1:n`
 |   **for** :math:`i=m:-1:j+1`
 |     :math:`R` = givens(:math:`A(i-1,j),A(i,j)`)
 |     :math:`A(i-1:i,j:n) = R^T A(i-1:i, j:n)`

We pick a rotation that introduces a zero at location :math:`(i,j)` and apply
it to rows ``i`` and ``i-1`` of :math:`A`, updating them in-place. Note that
the second loop counts down from :math:`m` to :math:`j+1`, and the arrays are
one-indexed.

The Plover code:

::

  qr_update {m, n}
    (inout b :: double[m])
    (inout A :: double[m, n])
    :: Void := (

      for j in 1 .. n,
          i in m .. j+1 : -1 -> (

        -- Givens rotation
        rot := givens A[i-2,j-1] A[i-1,j-1];
        -- Rotate one column at a time
        for k in j..n -> (
          v := A[i-2 .. i-1, k-1];
          A[i-2 .. i-1, k-1] <- rot^T * v;
        );

        -- Rotate b vector
        v := b[i-2 .. i-1];
        b[i-2 .. i-1] <- rot^T * v;

    );
  );

-------

::

  qr_update {m, n}
    (inout b :: double[m])
    (inout A :: double[m, n])

We use ``inout`` variables, mutating ``b`` and ``A`` as we go along. This way,
we never store the ``Q`` matrix and simply return the upper triangular rotation
of ``A``.

``{m, n}`` denotes that ``qr_update`` takes two implicit ``int``
parameters.  The function qr_update can be called simply with the (explicit)
``b`` and ``A`` arguments, and ``m`` and ``n`` will be inferred. If the
dimensions of the explicit arguments don't match, Plover will report a type
error. See the language reference for more details.

::

      for j in 1 .. n,
          i in m .. j+1 : -1 -> (

        -- Givens rotation
        rot := givens A[i-2,j-1] A[i-1,j-1];
        ...
      );

Plover uses zero-indexing, but we keep the same loop bounds to avoid too much
confusion in the translation.  The expression ``a..b`` denotes the sequence
of integers from ``a`` to ``b``, inclusive, whereas ``a:b`` excludes the upper
bound. The expression ``(a..b : -1)`` means: count from ``a`` to ``b`` with
step size -1.

::

        -- Rotate one column at a time
        for k in j..n -> (
          v := A[i-2 .. i-1, k-1];
          A[i-2 .. i-1, k-1] <- rot^T * v;
        );

We rotate one column at a time so that we can use a two element temporary
vector v to avoid overwiting elements of ``A`` while they are still needed by
the product computation.  Currently, Plover will not warn you and will not
automatically make a copy of the right hand side if one is needed to properly
compute an update statment ``a <- b``.

These lines also demonstrate the submatrix indexing facilities of Plover. We
often use the notation ``v[a:b]`` to take the subvector of ``v`` at indices
from ``a`` to ``b-1``.  These expressions can be used as l-values and as
r-values, as above. They can also be passed as ``out`` arguments to a function,
and the proper subvector will be updated.  We can take subranges of objects
with multiple indices as well: taking a row of a matrix is accomplished with
``M[i]`` or ``M[i, :]``, and taking a column is simply ``M[:, i]``. A colon
without upper or lower bounds is filled in appropriately.

Backsolving
-----------

Now we have a square upper triangular constraint matrix and a target vector; we can solve
this one row at a time, starting with the last.

For an upper-triangular system :math:`Rx=b`, the value of :math:`x_i` is given
by

.. math::

  x_i = \left. \left(b_i - \sum_{j=i+1}^n R_{ij}x_j\right)\middle/ R_{ii} \right. .


The algorithm will overwrite ``b[i]`` with this value, since it is not needed by
later steps.

::

  -- Back substitution for upper triangular U
  static backsolve {n}
    (U :: double[n,n])
    (inout b :: double[n])
    :: s8 := (
      for i in 0:n ->
        if U[i,i] == 0 then
          return -1;

      b[n-1] <- b[n-1]/U[n-1, n-1];

      for i in n-1 .. 1 : -1 -> (
        b[i-1] <- (b[i-1] - U[i-1, i : n] * b[i : n]) / U[i-1, i-1];
      );

      return 0;
  );

The ``*`` inside the for loop is shorthand for a dot product. We add a check to see if any of the
diagonal entries are 0 and return an error code as a signed byte.

Complete Solver
---------------

Finally, the completed algorithm:

::


  -- Assumes m >= n
  -- See "Matrix Computations" 4th ed. Golub and Van Loan
  qr_solve {m, n}
    (inout A :: double[m, n])
    (inout b :: double[m])

    (out solution :: double[n])
    (out residual :: double)

    :: s8 := (

    qr_update (inout b) (inout A);

    -- A is now upper triangular; backsolve it into b
    code := backsolve A[0:n, 0:n] (inout b[0:n]);

    -- Solution stored in first n elements
    solution <- b[0:n];

    -- Norm of error = norm of last m-n elements
    residual <- norm b[n:m];

    return code;
  );

Note the way implicit arguments are resolved.

The generated C:

::

  s8 qr_solve (const s32 m, const s32 n, double * A, double * b, double * solution, double * const residual)
  {
      qr_update(m, n, b, A);

      s8 code;
      double arg [n * n];
      double arg2 [n];

      for (s32 idx = 0; idx < n; idx++) {
          for (s32 idx2 = 0; idx2 < n; idx2++) {
              arg[n * idx + idx2] = A[n * idx + idx2];
          }
      }
      for (s32 idx = 0; idx < n; idx++) {
          arg2[idx] = b[idx];
      }
      code = backsolve(n, arg, arg2);
      for (s32 idx = 0; idx < n; idx++) {
          b[idx] = arg2[idx];
      }
      for (s32 idx = 0; idx < n; idx++) {
          solution[idx] = b[idx];
      }

      double arg3 [m - n];

      for (s32 idx = 0; idx < m - n; idx++) {
          arg3[idx] = b[n + idx];
      }
      *residual = norm(m - n, arg3);
      return code;
  }

The copying around ``inout b[0:n]`` is a bit inefficient in this case, but
similar logic is needed for more complex matrix storage types.

::

    // qr.h
    #ifndef PLOVER_GENERATED_qr
    #define PLOVER_GENERATED_qr

    #include "prelude.h"

    s8 qr_solve (const s32 m, const s32 n, double * A, double * b, double * solution, double * const residual);
    void qr_update (const s32 m, const s32 n, double * b, double * A);
    s32 main (void);


    #endif /* PLOVER_GENERATED_qr */

Citations
=========
.. [MC2013] G.H. Golub and C.F. Van Loan (2013). *Matrix Computations, 4th ed.* The Johns Hopkins University Press, Baltimore, MD.
