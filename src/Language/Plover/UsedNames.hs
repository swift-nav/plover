module Language.Plover.UsedNames
       where

import Language.Plover.Types
import Data.List
import Control.Monad.State

-- Facility to get all names from a program so that gensym can be sure
-- variables do not come from this set.

allToplevelNames :: [DefBinding] -> [Variable]
allToplevelNames dbs = nub $ dbs >>= allNamesInDefBinding

allNamesInDefBinding :: DefBinding -> [Variable]
allNamesInDefBinding db = [binding db] ++ allNamesInDefinition (definition db)

allNamesInDefinition :: Definition -> [Variable]
allNamesInDefinition (FunctionDef cexpr ft) = maybe [] allNames cexpr ++ allNamesInFunType ft
allNamesInDefinition (StructDef defs) = map fst defs
allNamesInDefinition (ValueDef cexpr t) = maybe [] allNames cexpr ++ allNamesInType t

allNames :: CExpr -> [Variable]
allNames (Vec _ v rng x) = [v] ++ allNamesInRange rng ++ allNames x
allNames (Return _ x) = allNames x
allNames (Assert _ x) = allNames x
allNames (RangeVal _ rng) = allNamesInRange rng
allNames (If _ a b c) = [a, b, c] >>= allNames
allNames (VecLit _ ty xs) = allNamesInType ty ++ (xs >>= allNames)
allNames (Let _ v d x) = [v] ++ allNames d ++ allNames x
allNames (Seq _ a b) = [a, b] >>= allNames
allNames (App _ f args) = allNames f ++ (args >>= allNames . unarg)
  where unarg (Arg x) = x
        unarg (ImpArg x) = x
allNames (ConcreteApp _ f args) = allNames f ++ (args >>= allNames)
allNames (HoleJ _ ty v) = allNamesInType ty ++ [v]
allNames (Get _ loc) = allNamesInLocation loc
allNames (Addr _ loc) = allNamesInLocation loc
allNames (Set _ loc v) = allNamesInLocation loc ++ allNames v
allNames (AssertType _ v t) = allNames v ++ allNamesInType t
allNames (Unary _ op x) = allNames x
allNames (Binary _ op x y) = allNames x ++ allNames y
allNames expr = []

allNamesInRange :: Range CExpr -> [Variable]
allNamesInRange rng = [rangeFrom rng, rangeTo rng, rangeStep rng] >>= allNames

allNamesInLocation :: Location CExpr -> [Variable]
allNamesInLocation (Ref t v) = allNamesInType t ++ [v]
allNamesInLocation (Index v idxs) = allNames v ++ (idxs >>= allNames)
allNamesInLocation (Field v _) = allNames v
allNamesInLocation (Deref v) = allNames v

allNamesInType :: Type -> [Variable]
allNamesInType (VecType idxs t) = (idxs >>= allNames) ++ allNamesInType t
allNamesInType (FnType ft) = allNamesInFunType ft
allNamesInType (PtrType t) = allNamesInType t
allNamesInType (TypedefType v) = [v]
allNamesInType (StructType v (ST members)) = [v] ++ (members >>= (\(mv, mt) -> [mv] ++ allNamesInType mt))
allNamesInType (TypeHole (Just v)) = [v]
allNamesInType t = []

allNamesInFunType :: FunctionType -> [Variable]
allNamesInFunType ft = let ((FnT args rt), _) = getEffectiveFunType ft
                       in (args >>= \(v, _, _, t) -> [v] ++ allNamesInType t) ++ allNamesInType rt
