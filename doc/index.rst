==============================================
                    Plover
==============================================
----------------------------------------------
High-level embedded linear algebra programming
----------------------------------------------

:Authors:  Scott Kovach, Kyle Miller
:Modified: August 2015

Plover is a programming language designed for compiling linear algebra
into robust, efficient C code suitable for running on embedded systems.

Plover generates code free of dynamic memory allocation and provides
compile-time checking of matrix and vector shapes using a lightweight
dependent type system.

Plover also aims to make use of sparse structure present in many
real-world linear algebra problems to generate more efficient code.


Documentation
=============

The Plover documentation is split into the following parts:

- The `Plover User Guide <guide.html>`_ gives installation
  instructions and general information about using the Plover
  compiler.
- The `Plover Tutorials <tutorials.html>`_ gives worked examples of
  programming algorithms and applications in Plover.
- The `Plover Language Reference <reference.html>`_ gives a more
  in-depth treatment of the language itself.


In the real world
=================

`Swift Navigation <http://www.swiftnav.com/>`_ uses Plover for
implementing GPS algorithms in `libswiftnav
<https://github.com/swift-nav/libswiftnav>`_.
