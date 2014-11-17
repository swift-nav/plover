## compile
- compiles expressions involving block vectors and products into imperative loops

## simplify
```haskell
data Expr e atom num = Expr
  { isSum :: e -> Maybe [e]
  , isMul :: e -> Maybe [e]
  , isAtom :: e -> Maybe atom
  , isPrim :: e -> Maybe num
  , zero :: num
  , one :: num
  }
```
- simplifies ring operations
- atom's are left intact
- prim's (num) should have a Num instance
