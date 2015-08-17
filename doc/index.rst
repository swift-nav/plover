==============================================
                    Plover
==============================================
----------------------------------------------
High-level embedded linear algebra programming
----------------------------------------------

:Authors:  Scott Kovach, Kyle Miller
:Modified: August 2015

Introduction
============

Plover is a programming language designed for compiling linear algebra
into robust, efficient C code suitable for running on embedded systems.

Plover generates code free of dynamic memory allocation and provides
compile-time checking of matrix and vector shapes using a lightweight
dependent type system.

Plover also aims to make use of sparse structure present in many
real-world linear algebra problems to generate more efficient code.

.. contents:: Table of Contents

Installation
============

First, install the `Haskell Platform
<https://www.haskell.org/platform/>`_ (recommended) or another GHC
7.10+ toolchain of your choice.

Check out the ``plover`` source:
::

   $ git clone https://github.com/swift-nav/plover.git
   $ cd plover

Next, create a cabal sandbox. This keeps any dependencies isolated so
you don't have to worry about conflicts with other versions you may
have on your system.
::

   $ cabal sandbox init

Install the dependencies into the sandbox:
::

   $ cabal install --only-dependencies --enable-tests

Run the test suite (requires ``gcc``):
::

   $ cabal test --show-details=streaming


Usage
=====

Plover may be used both as a traditional compilation pass or by using
Haskell as a macro language.

For help,
::

   $ plover -h


Tutorial
========

Reference
=========

Syntax
------

Sequencing
++++++++++

Unlike C, everything in Plover is an expression with a value (possibly
``void``).  Like C, the semicolon is the expression sequencing
operator.  Plover treats the final expression in a sequence as the
value of the sequence.  Hence,
::

   (a; b; c)

has value ``c``, after evaluating ``a`` and ``b`` (in that order).
Like other operators, parentheses are used to delimit sequences of
expressions (not curly braces, which are instead used to delimit
implicit function arguments).


Iteration constructs
++++++++++++++++++++


There are three basic iteration constructs in Plover: the ``for``
loop, the ``vec`` constructor, and the ``while`` loop

``for`` loop
~~~~~~~~~~~~

The ``for`` loop has the following basic syntax:
::

   for ${i} in ${range} -> ${body}

where ``i`` is the iteration variable, ``range`` is a range of some
type, and ``body`` is an expression to evaluate for each ``i`` in the
given range.  For instance,
::

   for i in 0:n -> printf "The variable i is currently %d\n" i;

Since multidimensional loops show up often enough, there is a special
syntax for specifying multiple indices in the same ``for`` construct.
For instance,
::

   for i in 0:n, j in 0:m -> printf "(i,j) = (%d,%d)\n" i j;

is equivalent to
::

   for i in 0:n ->
     for j in 0:n ->
       printf "(i,j) = (%d,%d)\n" i j;

The lower bound of a range may be omitted with a default of ``0``, so
the above may be shortend to ::

   for i in n, j in m -> printf "(i,j) = (%d,%d)\n" i j;

The value of the expressions in ``for`` can be of any type, but the
result of ``for`` is always void.

``vec`` constructor
~~~~~~~~~~~~~~~~~~~

The ``vec`` constructor has the same syntax as ``for``, and it
accumulates the values of the iteration as a location.  No guarantee
is made on the number of times any of the expressions in a ``vec``
will be computed, if the expressions are evaluated at all.  The type
of a ``vec`` expression is a dense matrix with base type the type of
the iterated expression.

This produces an identity matrix named `I`:
::

   I := vec i in n, j in n -> if i == j then 1 else 0;

``while`` loop
~~~~~~~~~~~~~~

The ``while`` loop is for iterating while a boolean condition remains
true.  There are two forms:
::

   while ${test} -> ${body};
   while ${test};

If the body is omitted, the body is assumed to be the empty
expression.

The ``while`` construct will

1. Evaluate the ``test`` expression;
2. If it is true, evaluate the ``body`` expression and return to step 1;
3. Otherwise, finish with the void value.

For instance, to binary search an array for a ``u8`` key:
::

   binary_search {n} (A :: u8[n]) (key :: u8) :: int
     := ( imin := 0; imax := n;
          while (imax >= imin) -> (
            imid := imin + (imax - imin) / 2;
            if A[imid] == key then
              return imid;
            else if A[imid] < key then
              imin <- imid + 1;
            else
              imax <- imid - 1;
          );
          return -1;
        );

The test in the ``while`` loop may be a sequence of statements, and so
the loop becomes like the do-while loop in C; the final expression in
the test sequence is the value used to determine whether another loop
iteration will occur.  For instance, here is an implementation of the
Box-Muller transform for normally distributed random numbers: ::

   rand_normal() :: double
     := ( x1 :: double; x2 :: double;
          w :: double;
          while (x1 <- 2 * rand_uniform() - 1.0;
                 x2 <- 2 * rand_uniform() - 1.0;
                 w <- x1 ^ 2 + x2 ^ 2;
                 
                 w >= 1.0);
          w <- sqrt( -2 * log w / w );
          return x1 * w;
        );


Value and type holes
++++++++++++++++++++

The Plover language supports introducing holes into a program which,
depending on context, may in some circumstances be filled during
normal typechecking.  This feature allows a programmer some
flexibility when prototyping and debugging.  The holes come in two
flavors: quiet and noisy.  The difference between the two is that
noisy holes will cause an error which will describe what the type
system believes may be a valid substitution for the holes, whereas
quiet holes will not cause an error so long as a valid substitution is
found.  The syntax for a quiet hole is a single underscore (``_``) and
for a noisy hole a double underscore (``__``).

A common example is in function parameter lists.  One may drop off the
types as in the following: ::

  foo (x :: _) :: _  := x + 1;

and because of defaulting rules, ``x`` will be ``int``, as is the
return type of ``foo``.

The following is the same as the above example: ::

  foo x :: _ := x + 1;

Noisy holes let a programmer see the type of intermediate results.
For instance, ::

  B :: __  := (G^T * G :: __)^(-1) * G^T;

to get the types of ``B`` and of ``G^T * G``.

Type system
-----------

The void type is the same as the type of empty tuples.

Vector types
++++++++++++

Compute :math:`v^TAv`

This is a math block

.. math::

   \alpha_t(i) = 2t+i

Modules
-------


Compiler options
----------------

There are options to the compiler, which you may discover with
::

   $ plover -h
