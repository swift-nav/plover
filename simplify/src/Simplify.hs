{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module Simplify
  (Expr(..), simplify, Poly)
where
import qualified Data.Map.Strict as M
import Control.Monad (foldM)
un = undefined

data Expr e atom num = Expr
  { isSum :: e -> Maybe [e]
  , isMul :: e -> Maybe [e]
  , isAtom :: e -> Maybe atom
  , isPrim :: e -> Maybe num
  , zero :: num
  , one :: num
  }

data Term atom n
  = Term n (M.Map atom Int)
  | Zero
  deriving (Show, Eq)
term1 :: Num n => Term atom n
term1 = Term 1 M.empty

-- Main simplification function
mul :: (Num n, Eq n, Ord atom) => Expr e atom n
    -> Term atom n -> e
    -> [Term atom n]
mul _ Zero _ = return Zero
mul e@Expr{..} term@(Term coef m) x = step x
 where
  mulOne x = M.insertWith (+) x 1
  --step a | Just (as, maker) <- isNode a =
  --  maker (map (simplify e) as)
  -- Distribute
  step a | Just as <- isSum a = concatMap (mul e term) as
  -- Sequence
  step a | Just as <- isMul a = foldM (mul e) term as
  -- Increment
  step a | Just a' <- isAtom a = return $ Term coef (mulOne a' m)
  -- Numeric simplify
  step a | Just n <- isPrim a =
    -- TODO is there an idiom for this?
    case undefined of
     _ | zero == n -> return Zero
     _ | one  == n -> return term
     _ -> return $ Term (n * coef) m

type ExponentList atom = [(atom, Int)]
flattenTerm :: Expr e atom n -> Term atom n -> (ExponentList atom, n)
flattenTerm Expr{zero} Zero = ([], zero)
flattenTerm _ (Term n m) =
  (M.toList m, n)
reduceProducts :: (Num n, Eq n, Ord atom) => Expr e atom n
               -> e -> [(ExponentList atom, n)]
reduceProducts e expr = map (flattenTerm e) $ mul e term1 expr

type Poly atom n = M.Map (ExponentList atom) n
poly0 :: Poly atom n
poly0 = M.empty

-- Calls mul, then gathers like terms
simplify :: (Num n, Eq n, Ord atom) => Expr e atom n
    -> e -> Poly atom n
simplify e@Expr{..} expr =
  let reducedTerms = reduceProducts e expr
      addOne (_, n) | zero == n = id
      addOne (term, n)  = M.insertWith (+) term n
  in foldr addOne poly0 reducedTerms
