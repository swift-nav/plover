module Language.Plover.Unify
       where

import Language.Plover.Types
import Data.List
import Control.Monad.State

-- Facility to get all names from a program so that gensym can be sure
-- variables do not come from this set.

allToplevelNames :: [DefBinding] -> [Variable]
allToplevelNames dbs = nub $ dbs >>= allNamesInDefBinding

allNamesInDefBinding :: DefBinding -> [Variable]
allNamesInDefBinding db = [binding db] ++ allNamesInDefinition (def db)

allNamesInDefinition :: Definition -> [Variable]
allNamesInDefinition (FunctionDef cexpr ft) = maybe [] allNames cexpr ++ allNamesInFunType ft
allNamesInDefinition (StructDef defs) = map fst defs
allNamesInDefinition (ValueDef cexpr t) = maybe [] allNames cexpr ++ allNamesInType t

allNames :: CExpr -> [Variable]
allNames (Vec v rng x) = [v] ++ allNamesInRange rng ++ allNames x
allNames (Return x) = allNames x
allNames (Assert x) = allNames x
allNames (RangeVal rng) = allNamesInRange rng
allNames (If a b c) = [a, b, c] >>= allNames
allNames (VecLit xs) = xs >>= allNames
allNames (Let v d x) = [v] ++ allNames d ++ allNames x
allNames (a :> b) = [a, b] >>= allNames
allNames (App f args) = allNames f ++ (args >>= allNames . unarg)
  where unarg (Arg x) = x
        unarg (ImpArg x) = x
allNames (ConcreteApp f args) = allNames f ++ (args >>= allNames)
allNames (Get loc) = allNamesInLocation loc
allNames (Set loc v) = allNamesInLocation loc ++ allNames v
allNames (AssertType v t) = allNames v ++ allNamesInType t
allNames (Unary op x) = allNames x
allNames (Binary op x y) = allNames x ++ allNames y
allNames expr = []

allNamesInRange :: Range CExpr -> [Variable]
allNamesInRange rng = [rangeFrom rng, rangeTo rng, rangeStep rng] >>= allNames

allNamesInLocation :: Location CExpr -> [Variable]
allNamesInLocation (Ref' t v) = allNamesInType t ++ [v]
allNamesInLocation (Index' v idxs) = allNames v ++ (idxs >>= allNames)
allNamesInLocation (Field' v _) = allNames v
allNamesInLocation (Deref' v) = allNames v

allNamesInType :: Type -> [Variable]
allNamesInType (VecType idxs t) = (idxs >>= allNames) ++ allNamesInType t
allNamesInType (FnType ft) = allNamesInFunType ft
allNamesInType (PtrType t) = allNamesInType t
-- structs?
allNamesInType t = []

allNamesInFunType :: FunctionType -> [Variable]
allNamesInFunType (FnT args rt) = (args >>= \(v, _, t) -> [v] ++ allNamesInType t) ++ allNamesInType rt



type Gensym = State ([Variable], Int)

gensym :: String -> Gensym Variable
gensym prefix = do (vs, i) <- get
                   let name = "$" ++ prefix ++ "_" ++ show i
                   if name `elem` vs
                     then do put (vs, i + 1)
                             gensym prefix
                     else do put (name:vs, i + 1)
                             return name

runGensym :: Gensym a -> [Variable] -> a
runGensym x avoids = evalState x (avoids, 0)

--dehole :: CExpr -> CExpr
