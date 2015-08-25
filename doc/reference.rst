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

The implementation in C for a vector type is simply ``T *``, where
``T`` is the C type for the base type of the vector, no matter how
many levels of storage types there are.

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

As is the case for many functional language, everything is an
expression in Plover: there is no distinction between statements and
expressions.  Expressions are sometimes called *statements*, partly
out of habit from using C-like languages, but this is generally
reserved for expressions which appear in a sequence.

.. note:: We will use ``${META}`` to denote metasyntactic variables,
   with ``META`` varying.  That is, this is not valid Plover
   expression, but instead denotes (as an analogy to shell scripting)
   some other code which should be spliced in this location.

Parentheses and Dollar
----------------------
   
Sequencing
----------

Unlike C, everything in Plover is an expression with a value (possibly
the void value ``()``).  Like C, the semicolon is the expression
sequencing operator.  Plover treats the final expression in a sequence
as the value of the sequence.  Hence, ::

   (a; b; c)

has value ``c``, after evaluating ``a`` and ``b`` (in that order).
Like for other operators, parentheses are used to delimit sequences of
expressions (not curly braces, which are instead used to delimit
implicit function arguments).  A sequence of expressions is sometimes
called a *block*.

Plover allows an optional dangling semicolon, as in ::

  (a; b; c;)

This is in no way functionally different from the previous sequence.

In a sequence, the results of the non-terminal expressions are
dropped, so in the following, the result of the first ``A + B`` is not
computed: ::

   ( printf "The quantity A+B is not computed.\n";
     A + B;
     printf "But the result following is if the value of this block is used.\n";
     A + B
   )


Variable Definitions
--------------------

There are two ways to define a new variable.  Both are done inside a
sequence, and the binding extends through the end of the sequence.
There must be some expression after the binding.

The first is for defining a new, uninitialized variable.::

  ( x :: ${Type};
    ${expressions} )

The variable ``x`` is declared to be of type ``Type`` (with some
reserved stack space) for the following expressions.

The second is for defining a new variable with an initial value.::

  ( x := ${value};
    ${expressions} )

or ::

  ( x :: ${Type} := ${value};
    ${expressions} )

The value is evaluated *before* the variable ``x`` is brought into
scope, and then the result is stored at the location for ``x``.

The type is optional because Plover is able to infer the type from the
value.  However, when dealing with integer or floating-point types it
can be useful to give a type when a specific width is wanted.

.. note:: Variables may not shadow other previous bindings.  There is
          no technical need for this other than the observation that
          accidental name shadowing can cause programmer errors.

Another example to demonstrate scoping rules: ::

  ( x := 22;
    y := x + 1;
    z := foo (&z); -- this is an error, since z is not bound on the r.h.s.
    w := ( b := 1;
           x := 23; -- this is an error, since x shadows x
           b + 100; );
    -- now w is 101
    c := b + 1; -- this is an error since b is no longer bound
  )

Ranges
------

There are two syntaxes for ranges of integers, each useful for
different circumstances, but in the end are equivalent.

The expression ``a:b`` represents all integers from ``a`` to ``b``,
excluding ``b``, where ``a..b`` represents all integers from ``a``
through ``b``, including ``b``.  The second syntax is especially
useful when implementing a numerical algorithm from a textbook.

Step sizes are specified using an extra ``:step``.  For instance,

::

   0:6     -- is 0,1,2,3,4,5
   0..6    -- is 0,1,2,3,4,5,6
   0:6:2   -- is 0,2,4
   0:5:2   -- is 0,2,4
   0..6:2  -- is 0,2,4,6
   0..5:2  -- is 0,2,4
   5:0:-1  -- is 5,4,3,2,1
   5:-1:-1 -- is 5,4,3,2,1,0
   5..0:-1 -- is 5,4,3,2,1,0

A benefit of ``:`` is that ``0:i`` and ``i:n`` together cover all
elements in ``0:n``.  On the other hand, ``1..i-1`` and ``i:n``
together cover all elements ``1..n``.

The type of a range expression is an integer-valued vector.

The lower bounds and upper bounds of a range can be omitted if Plover
is able to infer their values.  If the lower bound is omitted, it is
*always* assumed to be ``0``, so ``:6`` is the range ``0:6``.  If the
upper bound is omitted and is being used as an index, then it is
assumed to be the length that index of the vector.

.. note:: Textbooks tend to use 1-indexing of vectors and matrices,
          where C and Plover use 0-indexing.  (In some ways,
          1-indexing is about *naming* locations in a vector, where
          0-indexing is about *offsets* from the beginning of the
          vector, sometimes called a :math:`\mathbb{Z}`-torsor).

          A rule of thumb when translating: use 1-indexing and ``..``
          for loop bounds, and then subtract ``1`` whenever a vector
          is indexed (as this computes the *offset* from ``1``).  For
          instance,::

            for i in 1..n ->
              foo A[i-1];

          Trying to subtract one from the loop bounds is bound to give
          bounds errors.

Tuples
------

Tuples are a comma-separated list of values of varying types.  The
tuple with a single element is, like in Python, designated by using a
trailing comma.  The following are equivalent tuples: ::

  1,2
  1,2,
  (1,2)
  (1,2,)

These are all of type ``(int,int)``.  Notice that parentheses are
optional, and are only used for grouping.

One way to understand the tuple operator is as compared to sequences:
a sequence is like a tuple which drops all but the last element, and a
tuple is like a sequence which accumulates all elements of the
sequence.  However, a tuple makes no guarantee on evaluation order.

.. note:: Tuples are not yet implemented in full.  They cannot be
          stored, indexed, or passed as arguments.  They are used for
          indexing, however, as in ``A[1,2]``.

Locations
---------

Locations are places which can hold values.  Variables are a basic
kind of location, but there are other kinds of locations, too.

The first is from indexing.  Suppose ``A`` is some kind of location
which is vector typed, and ``i`` is some integer.  Then ``A[i]`` is
the location of row ``i`` of ``A``.  If ``A`` is a 1d vector, then
this is a scalar, but if it is a matrix, then it is the full row.
There are subtleties which will be discussed in its own section.

The second is from selecting a structure's field.  If ``o`` is of some
structure type, or a pointer to a structure, or a pointer to a pointer
to a structure (and so on), then ``o.f`` selects the ``f`` field from
``o``, like in C.  There is no need for ``->`` with pointers since
Plover can easily figure out when ``o`` is a pointer to a ... to a
struct.

The third is from dereferencing a pointer.  If ``p`` is some pointer,
then ``*p`` is the location ``p`` points to.

The ``<-`` operator assigns a value into a location by copying.  For
scalars and structs, it behaves like C assignment, but for vector
types it will generate the necessary loops to copy every element.  The
precise loops will depend on the type of the left-hand side, so, for
instance, assigning into a diagonal matrix type will only copy out the
diagonal of the right-hand side.

::

   A :: double[10];
   A <- vec i in 10 -> i; -- now A is filled with 0 through 9
   A[2] <- 22; -- now A[2] is 22
   B :: Diagonal double[11,11];
   B <- vec i in 11, j in 11 -> i * j; -- now B has i^2 on diagonal
   o :: MyStruct; -- suppose has field f
   o.f <- 100;
   z := &o;
   z.f <- 222;

Locations do not necessarily take stack space.  They will only take
stack space if an operator determines it will iterate over the
elements of a location multiple times.  This behavior can be
overridden with ``nomemo``.

Slices
~~~~~~

Vectors can be indexed by integer indices, tuple indices, vectors of
integer or tuple indices, or vectors of booleans.  As a running
example, suppose ``A`` has the type ``double[n,m]``.

First, the rule is that when applying indices to a vector, the
remaining indices are assumed to be ``:``.  Hence, ``A[1]`` is
``A[1,:]`` (which is ``A[1,0:m]``).

Second, indexing by an integer does what one would expect: take the
subvector of elements with that integer for the index.  So ``A[1,2]``
is the double on row 1, column 2.

Third, indexing by a tuple indexes by each of the components of the
tuple.  In fact, ``A[1,2]`` is syntactically the same as ``A[(1,2)]``.

Fourth, indexing by a vector of indices creates a new vector whose
indices are the indices of that index vector.  The expression
``A[1,0:m]`` is row 1 of the matrix, with type ``double[m]``.  The
expression ``A[0:n,1]`` is column 1 of the matrix, with type
``double[n]``.  The expression ``A[i..i+1,j..j+1]`` is a
``double[2,2]`` consisting of those elements in rows ``i`` and ``i+1``
and columns ``j`` and ``j+1``.

These rules make indexing by range expressions sound, but one can also
index by an arbitrary vector.  For instance, if ``I`` is any
``int[5]``, then ``A[I]`` is a matrix of type ``double[5,m]`` with the
rows of ``A`` indexed by ``I``.  Similarly, ``A[2,I]`` is a vector of
type ``double[5]`` of elements on row 2, the elements indexed by
``I``.

.. note::  Indexing by a vector of tuples is not yet implemented.

Indexing by an array of booleans acts as a filter expression which
masks the vector by treating all entries corresponding to ``False``
values as the default value for the type (for instance, ``0`` for
integers and floats).  The boolean indexing vector and the indexed
vector must match on each dimension, though the indexing vector may
have fewer dimensions than the indexed vector.  As an example, ::

  A[A < 0] <- 0;

sets all negative entries of ``A`` to ``0``, since ``A < 0`` is a
``bool[n,m]`` containing ``True`` exactly where ``A`` is non-negative.

Theoretically speaking, integer indices are like :math:`(0,1)` tensors
(i.e., no covariant indices and one contravariant index), because for
a standard basis vector ``E``, ``E[i]`` is :math:`0` unless ``E`` has
its :math:`1` at index ``i``.  Each extra element in a tuple index
corresponds to an extra contravariant index, and each extra index in
an indexing vector has corresponds to an extra covariant index for the
tensor.  With this, ``A[I]`` is tensor composition, and ``A[I,J]`` is
tensor composition of ``A`` and the tensor product of ``I`` with
``J``.  Limiting ourselves to only integers lets the tensor
composition be treated as a settable location (a more general indexing
scheme is possible, but less useful for general applications).


Type Specification
------------------

An expression can be asserted to have a particular type using the
``::`` operator.  The left-hand side is a value, and the right-hand
side is a type, as in Haskell.

This operator is also used for declaring the type of a new variable,
as described above for ``:=``.

The operator is useful for getting a particular integer or
floating-point type, as in ``5 :: s8``, but it can also be used to
ensure the programmer has the same understanding of the intermediate
types in an expression as Plover does.

Pointer Operators
-----------------

The ``*`` operator, as described in the locations section, takes a
pointer and gets the location which the pointer points to.  It is
prefix.

The (pseudo-)inverse of this operator is ``&``, which takes a location
and gives a pointer which can be later dereferenced by ``*``.

Since Plover treats scalar types and vector types differently, the
underlying implementation of ``*`` and ``&`` is different for
each. First of all, ``*T`` for a scalar type ``T`` is implemented as
``TT *`` in C, where ``T`` is the corresponding C type for ``T``.
When ``T`` is a vector type, then the C implementation of ``*T`` is
``TT``, since ``TT`` is already a pointer to the base type (as
described in the vector types section).  This rule keeps the number of
indirections down in the compiled C.

When ``&`` is applied to a vector location, Plover will guarantee
reified stack space for the location.  Plover will not guarantee any
modifications made to what that pointer points to will be reflected in
the original location, unless that location is just a reference.  That
is, ``&A[2:5,2]`` will not guarantee reflecting modifications, but
``&A`` will.

There is no arithmetic on pointer operators in Plover.  Pointers are
only useful for passing references to locations.

Operators
---------

These are listed in roughly decreasing order of precedence.

Exponentiation
~~~~~~~~~~~~~~

Written ``x^y``.  This is overloaded to have the following operations:

- When ``A`` is a matrix, ``A^T`` is the transpose of the matrix.
  ``T`` is a reserved word used especially for this syntax.  Taking
  the transpose requires no stack space.

  When ``A`` is an :math:`n`-dimensional vector, then ``A`` is
  presumed to be a :math:`n\times 1`-dimensional matrix for the
  purposes of transposition.
- When ``A`` is a matrix, ``A^(-1)`` is the inverse of the matrix.  If
  the matrix is singular, an error is raised using ``assert`` from
  ``assert.h``.  Taking the inverse requires stack space for the
  inverted matrix.
- When ``x`` and ``y`` are integers, then a C function ``ipow`` is
  called.  The Plover standard prelude gives an implementation.
- When ``x`` is floating-point and ``y`` is an integer, then a C
  function ``dipow`` is called.
- When ``x`` and ``y`` are floating-point numbers, then the C function
  ``pow`` from ``math.h`` is called.

Multiplication
~~~~~~~~~~~~~~

Written ``x*y``.  This is overloaded to have the following operations:

- When ``x`` and ``y`` are numerical scalars, then it is simply the product.
- When one is a product and the other is a numerical scalar, then it
  is a component-wise product.
- When ``x`` and ``y`` are matrices, then it is a matrix product.
  There are special implementations for different storage types for
  ``x`` and ``y``.  Depending on the dimensions of ``x`` and ``y``,
  the locations will be memoized on the stack.  In particular, if
  ``x`` has more than one row, then ``y`` will be memoized, and if
  ``y`` has more than one column, then ``x`` will be memoized. This
  behavior can be overridden with ``nomemo``.
- When ``x`` is a matrix and ``y`` is a vector, then it is a
  matrix-vector product.  Similar memoization rules apply.  Matrix
  storage types may give a special implementation, for instance when
  ``x`` is diagonal.
- When ``x`` and ``y`` are both vectors, then it is a dot product.

Element-wise Operations
~~~~~~~~~~~~~~~~~~~~~~~

The following are operators which can be applied on pairs of scalars,
or on vectors of varying sizes.  The vectors must either have the same
indices, or one of the vectors must be extendable to the other by
adding new indices to the front.  The operators are:

- ``a + b`` is the sum.
- ``a - b`` is the difference.
- ``a .* b`` is the Hadamard (pointwise) product.
- ``a / b`` is the quotient.

Auto-vectorization lets us compute things like ``1 + v`` to add ``1``
to each element of ``v``, or ``1/v`` to take the reciprocal of each
element.  Or, ``v+A`` for ``v`` a vector and ``A`` a matrix adds ``v``
to each row of ``A``.

The Hadamard product lets us compute a vector of the squares of
elements of a vector by ``v .* v``.

The following are unary element-wise operations:

- ``-a`` is the negation of each element of ``a``
- ``+a`` is each element of ``a``, but constrains ``a`` to being of
  numeric vector type.

Concatenation
~~~~~~~~~~~~~

The ``#`` operator takes two vectors and concatenates them along their
first index.  For two one-indexed vectors of types ``double[n]`` and
``double[m]``, the result is a ``double[n+m]``.  For two matrices of
types ``double[l,m]`` and ``double[n,m]``, the result is a matrix of
type ``double[l+n,m]``.

Inequalities
~~~~~~~~~~~~

The inequalities ``==``, ``!=``, ``<``, ``<=``, ``>``, ``>=`` all
operate on a pair of (vectors of) scalars and vectorize by the same
rules as the elementwise arithmetic operators, though the resulting
base type is ``bool``.

Boolean Operators
~~~~~~~~~~~~~~~~~

The operators ``and`` and ``or`` each take a pair of (vectors of)
booleans and give a boolean, where ``and`` has higher precedence than
``or``.  These follow the same elementwise vectorization rules.

The operator ``not`` takes a boolean or vector of booleans and gives
the boolean negation of the boolean(s).  It is parsed as a function,
and follows the same vectorization rules as unary arithmetic.

Function Application
--------------------

A function call is a function name followed by each of its arguments.
They are passed by juxtaposition, like in Haskell.  Implicit arguments
are optional if Plover can determine what they should be, but required
arguments must always be supplied.  A basic example is calling
``sqrt`` from prelude: ::

  sqrt 2

The precedence of function application is higher than any other
operator, so the following are equivalent: ::

  1 + sqrt 2 + 3
  1 + (sqrt 2) + 3

Implicit arguments, like in the function declaration, are delimited by
braces.  Suppose ``foo`` is declared as ::

  foo {n} (A :: double[n]) :: double;

and suppose ``B`` is a ``double[m]``.  Then the following are equivalent: ::

  foo B
  foo {m} B

If a function takes no arguments, a dummy void value must be supplied
as an argument, otherwise there is an ambiguity between function call
and variable value.  If ``do_it`` is a function of no arguments, this
looks like ::

  do_it ()

Argument Directions
~~~~~~~~~~~~~~~~~~~

Function arguments come in three flavors, ``in``, ``out``, and
``inout``.  By default, all arguments are ``in``, and so the above
could equivalently be written as ::

  foo (in B)
  foo {m} (in B)

The direction for the argument must match the declared direction for
the corresponding parameter of the function.

- ``in`` passes an argument by value.  The receiver is unable to
  change the value of any location passed in this way.  In the C
  interface for the compiled function, scalar types are passed by the
  standard C convention, and vector types are passed as constant
  pointers.  Plover will ensure that *any* location can be passed,
  including non-contiguous vector locations such as ``A[2,:]``, by
  copying the elements of the location to fresh stack space.
- ``inout`` passes an location by reference (or copy-restore of the
  location must be reified).  This means that any location passed in
  this way, if changed by the receiver, will have those changes
  reflected in the location by the time the called function returns.
  In the C interface for the function, scalar references are given
  pointer types, and vector types are *non*-constant pointers.  Plover
  will copy non-contiguous regions to fresh stack space before the
  call, and copy the region back into the original location after the
  call.
- ``out`` is like ``inout``, but the receiver may not use the value of
  the location, since the location is allowed to be uninitialized.

For example, the matrix inverse function in the prelude can be called
directly rather than through ``^(-1)`` by ::

  matrix_inverse {n} A (out B) -- returns -1 if A is singular

Of course, the ``{n}`` is optional.

C interface note: when a function returns a vector, it is actually
represented as an ``out`` variable, and the caller must allocate stack
space for the returned vector.


Iteration Constructs
--------------------

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
--------------------

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

- Quasiquotation.  This feature would let a user create macros.
  ::
     
     -- Macros.hs
     {-# LANGUAGE QuasiQuotes #-}
     module Macros where
     import Language.Plover.Quote
     import Language.Plover.ParserTypes
     
     square :: Expr -> P Expr
     square x = do t <- gensym "t"
                   return [pexp| (~t := ~x; ~t * ~t) |]

  ::
     
     -- Lib.plv
     
     {-# import Macros #-}
     
     use_square (z :: double) :: double :=
       ~(square [pexp| z |]);

  The effective ``Lib.plv`` after macro expansion would be
  ::
   
     -- Lib.plv
     use_square (z :: double) :: double :=
       (t22 := z; t22 * t22);

  A good application would be generating code for specialized matrix
  inverses.

- Delimited location pointers.  Since ``&`` does not guarantee
  reflecting changes back to a Plover location, there is a proposal to
  introduce a block-delimited pointer constructor: ::

    with_pointer p from A[2:5,2] -> (
      use_pointer p;
    );
    -- here changes to *p are reflected in A
