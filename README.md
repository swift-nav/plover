Plover
======

Plover is an embedded Haskell DSL for compiling linear algebra into robust,
efficient C code suitable for running on embedded systems.

Plover generates code free of dynamic memory allocation and provides compile
time checking of matrix and vector shapes using a lightweight dependant type
system.

Plover also aims to make use of sparse structure present in many real world
linear algebra problems to generate more efficient code.

 - `Plover.Types` contains the AST for the DSL.
 - `Plover.Expressions` contains a number of example expressions.
 - `Plover.Reduce` contains the main compiler.
 - `Plover.Macros` contains DSL utilities.

Installation
------------

First, install the [Haskell Platform](https://www.haskell.org/platform/)
(recommended) or other GHC 7.10+ toolchain of your choice.

Check out the `plover` source:

```
$ git clone https://github.com/swift-nav/plover.git
$ cd plover
```

Next, create a cabal sandbox. This keeps any dependencies isolated so you don't
have to worry about conflicts with other versions you may have on your system.

```
$ cabal sandbox init
```

Install the dependencies into the sandbox:

```
$ cabal install --only-dependencies --enable-tests
```

Run the test suite (requires gcc):

```
$ cabal test --show-details=streaming
```

Usage
-----

See
http://swift-nav.github.io/plover/guide.html

