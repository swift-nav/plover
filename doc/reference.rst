===========================
 Plover Language Reference
===========================

:Authors:  Scott Kovach, Kyle Miller
:Modified: August 2015

Overview
========

This is a reference manual for the Plover programming language.
Plover was designed for describing matrix algebra on embedded systems,
but it has some capacity for systems programming.

The language targets C and aims to be compatible with C conventions
for ease of integration in existing projects.  Unlike LAPACK, Plover
has embedded systems in mind and gives some care to stack utilization.

The reference manual covers the language itself.  See the `User Guide
<guide.html>`_ for documentation about Plover the toolchain.

.. contents:: Table of Contents

Syntax Elements
===============

Identifiers
-----------

Identifiers are sequences of characters for naming variables,
functions, and data types.  They are a nonempty sequences of letters,
digits, underscores, and single quotes, where the first character must
be a letter or underscore.

In short: they are C identifiers which may also contain single quotes
after the first character.

Identifiers which name top-level definitions must also be valid as C
identifiers.

The single quote allows identifiers such as ``x'`` (pronounced "ex
prime"), which can be convenient in mathematical expressions.

Reserved names
--------------

Reserved names are special identifiers which are reserved for the
programming language, and may not be used for any other purpose.

This is the list of reserved names:

::
   
   module import extern static inline __C__
   struct type storing
   mat vec for in out inout
   while if then else specialize
   True False Void T _ __
   and or return assert

Operators
---------

An operator is a special sequence of symbols which represents an
operation, such as addition or multiplication, on one or two operands.
Operators are parsed greedily, so ``x<-2`` is *not* the comparison
between ``x`` and ``-2``, but rather storing ``2`` into ``x``.

Operators will described in more detail later.

Constant Literals
-----------------

Like in C, Plover provides syntax for basic data such as numbers and
strings.  The syntax for literals is derived from Haskell.

Integers
~~~~~~~~

Integer literals are given by a sequence of digits, possibly with
prefixed base specifier.

Hexadecimal literals are prefixed by ``0x`` or ``0X``, and octal
literals are prefixed by ``0o`` or ``0O``.  Unlike C, a ``0`` prefix
by itself does not designate an octal base, so ``022`` is equal to
``22`` (rather than ``18``).

The type of an integer literal defaults to ``s32`` if otherwise
unspecified by context.

These are examples of integer literals:
::

   22
   0x16
   0o26

Floating-Point Numbers
~~~~~~~~~~~~~~~~~~~~~~

A floating-point number is a nonempty sequence of digits, followed by
at least a fractional part, an exponent, or both a fractional part and
an exponent:

1. A fractional part is a dot (``.``) followed by a nonempty sequence of digits.
2. An exponent is either ``e`` or ``E``, optionally followed by a sign, and then a
   nonempty sequence of digits.

The type of a floating-point literal defaults to ``double`` if
otherwise unspecified by context.

These are examples of floating-point literals:
::

   22.2
   2.22e1
   222e-1

Booleans
~~~~~~~~

The Boolean literals are ``True`` and ``False`` for the concepts of
being true and of being false, respectively.

Void
~~~~

The void literal, which is the sole value inhabiting the void type, is
represented equivalently by either ``Void`` or ``()``.

Strings
~~~~~~~

String literals use the Haskell definition in `section 2.6
<https://www.haskell.org/onlinereport/lexemes.html#sect2.6>`_ of the
Haskell 98 Report.  This is similar to C, but with the addition that
strings may have a "gap" of ignored backslash-enclosed whitespace.
For instance, ``"hello, \ \world!"`` is equivalent to ``"hello,
world!``.  Gaps may contain newlines, so the following is also
equivalent:
::

   "hello, \
        \world!"


Whitespace
----------

Whitespace is not significant except for the purpose of separating
identifiers and reserved names.

Comments
~~~~~~~~

Comments are treated as whitespace and have the same syntax as in
Haskell.

End-of-line-terminated comments are initiated with a double hyphen
(``--``), and are the equivalent of C-style double forward slash.  The
new line in such a comment cannot be escaped as they may in C.

Nested comments are delimited by ``{-`` and ``-}`` (the equivalent of
``/*`` and ``*/`` in C).  Nested comments may be nested to any depth.
In an ordinary comment, ``{-`` and ``-}`` have no special
significance.
::

   -- this is a comment at the beginning of the line
   x := 22; -- this is a comment later in the line
   {- this is a nested comment
      -- ordinary comments have no special significance inside a nested comment -}
   y := 23; -- this is outside the nested comment
   {- nested comments {- may be {- nested -} -} -}
   
   ---
   --- Multiple hyphens may be used
   ---

   {--- in nested comments as well ---}

.. warning:: When commenting out a section of code with ordinary
   comments, any nested comment symbols which may occur in the
   ordinary comments may interfere with the nesting.  For instance,
   the following is a likely error: ::

     {-
       x := 22;
       y := 23; -- Usually -} is ok in an ordinary comment
     -}


Types
=====

Every value in Plover has an associated type.  The type system is able
to accommodate parts of the C type system as well as a richer set of
vector/matrix types.

Integer Types
-------------

Integers can be signed or unsigned of the standard bit widths 8, 16,
32, and 64.  They are denoted by ``s8``, ``u8``, ``s16``, ``u16``,
``s32``, ``u32``, ``s64``, and ``u64``.  The type ``int`` is also
available, and it represents the default integer type, which defaults
to ``s32`` unless otherwise constrained.

Plover expects these types to be defined in the C environment, and
there are implementations in the default ``prelude.plv``.

.. note:: The standard C arithmetic rules apply, and Plover assumes
   the target system has a 32-bit ``int``.

Floating-Point Types
--------------------

There are two floating-point types, ``float`` and ``double``, which
represent the types of 32- and 64-bit IEEE floating-point numbers,
respectively.  As in C, arithmetic defaults to ``double``.

Boolean Type
------------

The type of boolean values is ``bool``.  Plover uses ``bool`` from
``stdbool.h`` for the implementation.

String Type
-----------

The string type is denoted by ``string``.  Plover uses ``char *`` for
their C implementation.

Pointer Types
-------------

A pointer is a value which represents the location to a value.  The
syntax for a pointer to something of type ``T`` is written ``*T``
(unlike in C, where the ``*`` is written after the type; this is so
that ``*`` always is a prefix operator for both types and values).

Since Plover treats the locations of vector and scalar types
differently, the underlying implementation of pointers is treated
differently in each case as well.  This will be discussed in the
section on the ``*`` and ``&`` operators.

Vector Types
------------

A vector type, in its basic form, with base type ``T``, is written as
``T[n1,...,nm]`` to create a (dense) vector with ``m`` indices (also
known as bounds).  For instance, the type of a five by three dense
matrix is written ``double[5,3]``.

.. warning:: The type ``double[5][3]`` is not the same as
             ``double[5,3]``.  The former is a vector of three vectors
             of five, where the second is a vector of 5 vectors of 3.

.. note:: The brackets are syntactically an index applied to the base
          type.  In C it is more complicated.

Vectors may have different underlying storage formats to take
advantage of properties of the vector or matrix.  For a given storage
type ``S``, the syntax of vector with the given storage type is ``S
T[n1,...,nm]``.  This is parsed with the same precedence of function
application.

A matrix is simply a vector type with two indices.  When it is not
otherwise confusing to say so, a vector is a vector type with one
index.

These are the known storage types:

- ``Dense`` is for dense matrices where every element is stored.  They
  are stored row-normal, and can have any number of indices.  This
  storage type is the default result of operations on vectors.
- ``Diagonal`` stores only the diagonal of a matrix, and it is
  presumed that every other non-diagonal element is zero.  Diagonal
  matrices **must** be square.
- ``UpperTriangular`` stores only the upper triangular portion of a
  matrix in packed column-normal form.  They **must** be square.  An
  ``UpperTriangular T[n,n]`` is stored in a C array with ``n * (n + 1) / 2``
  entries.
- ``LowerTriangular`` stores only the lower triangular portion of a
  matrix in packed row-normal form.  It has the same storage
  considerations as ``UpperTriangular``.
- ``Symmetric`` stores the lower triangular portion of a symmetric
  matrix, where the upper triangular portion is derived from the lower
  portion.  The storage is the same as ``LowerTriangular``.
- ``Scalar`` stores a diagonal matrix whose diagonal is a single
  constant.  The underlying storage holds only a single element.  Such
  matrices are also known as *homotheties* or *dilations*.  These also
  **must** be square.

.. note:: Generally speaking, the storage types may have *any* type
          for the base type of the vector, so, while questionable in
          utility, it is possible to have ``Symmetric (Diagonal
          (double[o,p])[n,n])[m,m]`` for an ``m`` by ``m`` symmetric
          matrix of ``n`` by ``n`` diagonal matrices of dense ``o`` by
          ``p`` matrices.

The effective type of a vector for the purposes of an arithmetic
operation is the dense version with all of the indices concatenated
appropriately, since the underlying storage is merely an
implementation detail.  For instance, the effective type of the vector
in the note is ``double[m,m,n,n,o,p]`` (i.e., a 6-index tensor).

Tuple Types
-----------

The type of a tuple uses the same syntax as a tuple value, but with
some number of types.  So, ``(double, int)`` is the type for pairs
whose first element is a double and whose second element is an
integer.

.. warning:: Tuples have limited implementation in Plover at the
             moment.  For now, ``struct`` can substitute some uses.

One particular tuple type is very important, and it is ``()`` (with
alias ``Void``), which is the tuple of no subtypes.  In the C
implementation, this type is compiled as ``void``, and, like in C,
does not actually have a reifiable value.

Function Types
--------------

The type of a function cannot be written in Plover, though all
functions have a type.  The type is the types of each of the
parameters declared for the function, whether each is implicit or
explicit, whether each is ``in``, ``out``, or ``inout``, what the type
of the variadic parts are (if the function is variadic), and the
return type of the function.  See the section on top-level function
definitions for more information.

Struct Types
------------

Structures are named types with a collection of fields (also known as
members) with types.

Since Plover is meant to interoperate with C, each field has an
internal and external type.  The external type describes to C how the
object should be represented in memory, and the internal type
describes to Plover how to interact with the value.  This separation
is mainly useful for vector types.  See the section on dependent types
and the ``storing`` reserved name.

Type Holes
----------

Type holes are unknown types which are solved by the unification
algorithm in the plover compiler.  See the section on type and value
holes.

Expressions and Operators
=========================

Syntax
------

Sequencing
~~~~~~~~~~

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
~~~~~~~~~~~~~~~~~~~~


There are three basic iteration constructs in Plover: the ``for``
loop, the ``vec`` constructor, and the ``while`` loop

``for`` loop
++++++++++++

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
+++++++++++++++++++

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
++++++++++++++

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
~~~~~~~~~~~~~~~~~~~~

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


Top-level Definitions
=====================

Functions
---------

Structs
-------

Typedefs
--------

Modules
=======

Language Proposals
==================

This is a short list of future language extensions which have not yet
been implemented.

- Block matrix storage types.  These would be given by
  ``Block(T1,T2;T3,T4) T5`` to say that type ``T5`` is represented by
  storing the components into submatrices of types ``T1`` through
  ``T4``.  An example would be ``Block(LowerTriangular double[n,n],
  Scalar double[n,n]; Scalar double[n,n], LowerTriangular double[n,n])
  double[2*n,2*n]``.
