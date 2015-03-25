`plover` compiles matrix arithmetic written in an embedded DSL into C code.

`Plover.Types` contains the AST for the DSL.
`Plover.Expressions` contains a number of example expressions.
`Plover.Reduce` contains the main compiler.
`Plover.Macros` contains DSL utilities.

`cabal repl` will load `Plover.Compile`, `Plover.Expressions`, and other modules.
Experiment with the `printExpr` function.

`cabal repl test-rewrites` will load the tests. run them with `main`. Running
tests requires gcc.
