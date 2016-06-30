========================================
Notable Differences from Other Languages
========================================

:Authors:  Scott Kovach
:Modified: June 2016

:= vs <-
========

The familiar assignment operator from C, ``=``, splits into two forms in
plover: ``:=, <-``. In short, ``:=`` is used to declare and initialize a
variable (whose type will generally be inferred), while ``<-`` is used to
mutate a variable already in scope.

See definitions_ and locations_.

Value of a Block
================

As described in sequencing_, the value of a sequence expression ``(a ; b)`` is
the value of ``b``. A common error is to call a function as the last statement
of a block which is intended to have void type.

For instance, ::

  f (x :: int) :: () := (
    printf "x: %d" x;
  );

will produce an error, because the (often ignored) return type from printf is
actually ``int``. The simplest fix in this case is to add a void literal,
``()``: ::

  f (x :: int) :: () := (
    printf "x: %d" x; ();
  );

Another consequence of this convention is that the ``return`` keyword is
optional on the last statement of a function. It is still useful as an early
return mechanism, of course. 

if/then/else
============

The branches of an ``if`` expression must have the same type. When the ``else`` branch is omitted, it has void type. Hence ::

  if condition then printf "hi there\n";

is incorrect.

Notably, when ``return`` is used, the expression being returned is checked
against the return type of the enclosing function, but the type of the
``return`` expression itself changes to match what is expected by its immediate
context.  Thus, the following is ok: ::

  f (x :: int) :: int := (
    if x > 0 then return x;
    return -x;
  );

but, when possible, this is a better style: ::

  f (x :: int) :: int := if x > 0 then x else -x;

.

Delimiters
==========

A block is typically delimited with parentheses: ``(a; b; ...)``. Semicolons
(``;``) must separate statements within a block. Top-level definitions and
``extern`` definitions are, likewise, separated by semicolons.

.. warning:: In the face of a troubling parsing or typechecking error, make sure you haven't
  left out any semicolons.

Vectors and Matrices
====================

The size of a vector object is represented, internally, as a list of Plover
expressions. Each position in this list is called an "index", and the
expression at a given index is called a "bound" or a "dimension." This is meant
to coincide with the usual language for discussing tensors. We will refer to
the number of indices as the object's rank.

Generally we call rank-1 and rank-2 objects vectors and matrices, respectively.

Plover overloads multiplication_ to handle certain frequent use cases. In
particular, for a matrix-vector product ``(M*v)``, the vector is interpreted as
a column vector. The vector-matrix product is not implemented; instead, you may
use ``(v^T*M)``. Note that the builtin transpose operator converts a rank-1
vector of dimension ``n`` into an explicit, rank-2, ``[1,n]`` matrix. For this
reason, taking a transpose twice may not return an object identical to the
initial one. Some discussion on the complexity of this issue: julia_.

Indexing
========

Plover indexing is 0-based. Matrices are row-major. See ranges_ and slicing_
for more information.

References
==========

.. target-notes ::
.. _definitions: http://swift-nav.github.io/plover/reference.html#variable-definitions
.. _locations: http://swift-nav.github.io/plover/reference.html#locations
.. _sequencing: http://swift-nav.github.io/plover/reference.html#sequencing
.. _multiplication: http://swift-nav.github.io/plover/reference.html#multiplication
.. _ranges: http://swift-nav.github.io/plover/reference.html#ranges
.. _slicing: http://swift-nav.github.io/plover/reference.html#slices
.. _julia: https://github.com/JuliaLang/julia/issues/4774
