===================
 Plover User Guide
===================

:Authors:  Scott Kovach, Kyle Miller
:Modified: August 2015

This part of the documentation describes how to install and use the
Plover compiler.

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


Compiler options
================

There are options to the compiler, which you may discover with
::

   $ plover -h
