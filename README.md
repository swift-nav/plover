Plover
======

`plover` compiles matrix arithmetic written in an embedded DSL into C code.

 - `Plover.Types` contains the AST for the DSL.
 - `Plover.Expressions` contains a number of example expressions.
 - `Plover.Reduce` contains the main compiler.
 - `Plover.Macros` contains DSL utilities.

Installation
------------

First, install the [Haskell Platform](https://www.haskell.org/platform/)
(recommended) or other GHC 7.8+ toolchain of your choice.

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

`cabal repl` will load `Plover.Compile`, `Plover.Expressions`, and other modules.
Experiment with the `printExpr` function.

`cabal repl test-rewrites` will load the tests. run them with `main`. Running
tests requires gcc.

