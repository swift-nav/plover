==================
 Plover Tutorials
==================

:Authors:  Scott Kovach, Kyle Miller
:Modified: August 2015

This part of the documentation gives worked examples of using Plover.

.. contents:: Table of Contents

Programming a QR Least Squares Solver
=====================================

We're going to step through the implementation of a textbook algorithm: a QR
least squares solver for overdetermined systems. That is, given :math:`A\in
\R^{m\times n}` and :math:`b\in \R^m` with :math:`m \geq n`, we want to find a
vector :math:`x\in\R^n` such that the squared error :math:`\norm{Ax-b}` is
minimized.

The essential steps are:

1. Apply orthogonal transformations to :math:`A` and :math:`b` until
   :math:`A`'s first :math:`n` rows are upper triangular.
2. Backsolve the triangular system.
3. Return the solution and the error (the norm of the last :math:`n-m` entries
   of :math:`b`).

We will attempt to mindlessly follow the implementation given in [MC2013]_.

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

| givens(a, b) **returns** [:math:`c, s`]
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

breaking it down:

::

  static givens (a :: double) (b :: double) :: double[2,2] := (
    ...
  );

Plover is statically typed, and all functions require a type signature,
although in many cases types can be inferred (see the section on type holes).
The function signature indicates that the function ``givens`` is ``static``
(not exported in the header) takes two arguments ``a`` and ``b`` of type
``double``, and returns a 2-by-2 matrix of doubles.  Function declarations and
variable initializations use the ``:=`` operator, and blocks are encosed within
parentheses. The statements of a block are separated by semicolons. Function
declarations must also be terminated by a semicolon.

::

    c :: double;
    s :: double;


A new local variable may either be declared with a type or with an initial
value, in which case the type will be inferred.  In this case, ``c`` and ``s``
will be set by some branch of the ``if`` statement below, so we simply declare
them with a type.

::

    if b == 0 then (
      c <- 1; s <- 0
    )

The condition of an ``if`` statement does not need enclosing parentheses. The
condition must be followed by the keyword ``then`` and an expression or
statement. In this case, we have a block which updates the values of ``c`` and
``s``.  Updating variables must be done with ``<-`` .

::

    else if fabs b > fabs a then (
      tau := -a/b; s <- 1/sqrt(1+tau*tau); c <- s*tau
    ) else (
      tau := -b/a; c <- 1/sqrt(1+tau*tau); s <- c*tau
    );

``if`` statements are optionally followed by an ``else`` clause and another
expression or block. Here, the ``fabs`` function is called on ``b`` and ``a``,
and these values are compared to choose the branch.  The local ``tau`` is
initialized, and ``c`` and ``s`` are updated as shown in the pseudocode above.
The ``fabs`` and ``sqrt`` functions are included in Plover's ``prelude``
module.

::

    mat( c, s ;
        -s, c );

The final expression in a block is treated as the value for that block. Here,
the function returns a 2-by-2 matrix literal containing the values we've just computed.


Let's take a look at the C code generated so far:


Citations
=========
.. [MC2013] G.H. Golub and C.F. Van Loan (2013). *Matrix Computations, 4th ed.* The Johns Hopkins University Press, Baltimore, MD.
