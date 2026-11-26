{-|
Module      : The untyped lambda-calculus
Description : Terms, substitution, evaluation.

An Haskell adaptation of the code for Types and Programming Languages (TAPL), by
Benjamin Pierce, The MIT Press (2002), except for substitution which is taken
from Hindley, J.R., Seldin, J.P.: Introduction to Combinators and
Lambda-Calculus, Cambridge University Press (1986)

Fundamentals of Programming Languages
MSc in Informatics Engineering
Faculty of Sciences
University of Lisbon
2026/27
-}

module UntypedLambda where

import qualified Data.Set as Set
import Prelude hiding (id, and, or, not, fst, snd, succ)

-- Names for variables
type Id = String 

data Term =
    Var Id
  | Abs Id Term
  | App Term Term

instance Show Term where -- with special support for some constants
  show (Var x) = x
  show (Abs x (Var y)) | x == y = "id"
  show (Abs x (Abs y (Var z))) | x /= y && x == z = "true"
  show (Abs x (Abs y (Var z))) | x /= y && y == z = "false"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Abs x t) = "(λ" ++ x ++ "." ++ show t ++ ")"

-- The set of the free variables in a term
freeVars :: Term -> Set.Set Id
freeVars = error "To be defined"

-- A fresh variable name, that is, a variable name that is not present in a set
-- of variables.
newId :: Set.Set Id -> Id
newId vs = head [v | n <- [0..], let v = '_':show n, v `Set.notMember` vs]

-- Substitution as in the books of Curry and Feys and Hindley and Seldin. The
-- first and the last equation for Abs are not in TAPL, for TAPL assumes the
-- variable convention, something Haskell cannot.
subs :: Id -> Term -> Term -> Term
subs x s (Var y)
  | y == x    = s
  | otherwise = Var y
subs x s (Abs y t)
  -- No need to continue in this case
  | x == y = Abs y t
  -- The easy case
  | y /= x && (y `Set.notMember` fvS || x `Set.notMember` fvT) = Abs y (subs x s t)
  -- Rename if danger of variable capture
  | otherwise = Abs z (subs x s (subs y (Var z) t))
  where fvS = freeVars s
        fvT = freeVars t
        z = newId (fvS `Set.union` fvT)
subs x s (App t1 t2) = App (subs x s t1) (subs x s t2)

-- Examples of substitution

-- "Lambda-Calculus and Combinators: An Introduction" by Hindley and Seldin
t1, t2, t3, t4, t5, t6, t7, t8 :: Term
t1 = subs "x" (Var "w") (Abs "w" (Var "x"))
t2 = subs "x" (App (Var "u") (Var "v")) (Abs "y" (App (Var "x") (Abs "w" (App (Var "v") (App (Var "w") (Var "x"))))))
t3 = subs "x" (Abs "y" (App (Var "v") (Var "y"))) (App (Var "y") (Abs "v" (App (Var "x") (Var "v"))))
t4 = subs "x" (Abs "_0" (App (Var "_1") (Var "_0"))) (App (Var "_0") (Abs "_1" (App (Var "x") (Var "_1"))))
-- TAPL, page 70
t5 = subs "x" (Var "y") (Abs "x" (Var "x"))
t6 = subs "_0" (Var "_1") (Abs "_0" (Var "_0"))
-- Others
t7 = subs "x" (Var "z") (Abs "z" (Var "x"))
t8 = subs "_0" (Var "_1") (Abs "_1" (Var "_0"))

