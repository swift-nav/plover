========
 Plover
========

.. compile docs with $ rst2html.py index.rst index.html

:Authors:  Scott Kovach, Kyle Miller
:Modified: August 2015

.. contents:: Table of Contents

Introduction
============

Plover is a programming language designed for compiling linear algebra
into robust, efficient C code suitable for running on embedded systems.

Plover generates code free of dynamic memory allocation and provides
compile-time checking of matrix and vector shapes using a lightweight
dependent type system.

Plover also aims to make use of sparse structure present in many
real-world linear algebra problems to generate more efficient code.

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

Type system
-----------

Vector types
++++++++++++

Modules
-------


Compiler options
----------------
