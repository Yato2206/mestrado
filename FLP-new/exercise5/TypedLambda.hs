{-|
Module      : The typed lambda-calculus
Description : Terms, substitution, evaluation, types, typing.

A Haskell adaptation of the code for Types and Programming Languages (TAPL), by
Benjamin Pierce, 2002, The MIT Press.

Fundamentals of Programming Languages
MSc in Informatics Engineering
Faculty of Sciences
University of Lisbon
2026/27
-}

module TypedLambda where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Prelude hiding (and, or, not, fst, snd)
-- Uncomment for the exercise on erasure; requires your module UntypedLambda
-- from Exercises 4
-- import qualified UntypedLambda as U

data Type =
    A               -- base type, Figure 11-1, page 118
  | Arrow Type Type
  deriving Eq

instance Show Type where
  show A = "A"
  show (Arrow t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"

-- Names for variables
type Id = String

data Term =
-- Figure 9-1, page 103
    Var Id
  | Abs Id Type Term
  | App Term Term

instance Show Term where
  show (Var x) = x
  show (Abs x u t) = "(λ" ++ x ++ ":" ++ show u ++ "." ++ show t ++ ")"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"

-- The free variables of an expression
freeVars :: Term -> Set.Set Id
freeVars (Var x)       = Set.singleton x
freeVars (Abs x _ t1)  = Set.delete x (freeVars t1)
freeVars (App t1 t2)   = freeVars t1 `Set.union` freeVars t2

-- [x -> s]t. Substitution, as in TAPL, def 5.3.5, page 71, but with on-the-fly
-- renaming when y in freeVars(s) and x in freeVars(t)
subs :: Id -> Term -> Term -> Term
subs x s (Var y)
  | y == x    = s
  | otherwise = Var y
subs x s (Abs y τ t)
  -- Optimise
  | x == y = Abs y τ t
  -- The easy case
  | y `Set.notMember` fvS || x `Set.notMember` fvT = Abs y τ (subs x s t)
  -- Rename if danger of variable capture
  | otherwise = Abs z τ (subs x s (subs y (Var z) t))
  where fvS = freeVars s
        fvT = freeVars t
        z = newId (fvS `Set.union` fvT)
subs x s (App t1 t2) = App (subs x s t1) (subs x s t2)

-- A fresh variable name that is, a variable name that is not present in a set
-- of variables
newId :: Set.Set Id -> Id
newId vs = head [v | n <- [0..], let v = '_':show n, v `Set.notMember` vs]

-- values
value :: Term -> Bool
-- Figure 9-1, page 103
value Abs{} = True
value _ = False

-- single-step evaluator
-- Partial: undefined on values and on variables (no rule applies)
step :: Term -> Term
-- Figure 9-1, page 103
step (App (Abs x _ t1) v2) | value v2 = subs x v2 t1      -- E-AppAbs
step (App v1 t2)           | value v1 = App v1 (step t2) -- E-App2
step (App t1 t2)                      = App (step t1) t2 -- E-App1

-- multi-step evaluator
-- Precondition: t is closed and well typed (in the empty context), so that,
-- by progress, t is either a value or else it takes a step
eval :: Term -> Term
eval t
  | value t = t
  | otherwise = eval (step t)

-- TYPING

type Context = Map.Map Id Type

typeof :: Context -> Term -> Type
-- Figure 9-1, page 103
typeof = error "To be defined"

-- SOME TERMS

-- Use typeof to check the types of your terms. Note that no closed term has
-- type A, so test and pair cannot be applied to closed arguments.

-- Church booleans, page 58
boolT :: Type
boolT = error "To be defined"

tru, fls, test, and, or, not :: Term
tru = error "To be defined"
fls = error "To be defined"
test = error "To be defined"
and = error "To be defined"
or = error "To be defined"
not = error "To be defined"

-- Pairs, page 60
pairT :: Type
pairT = error "To be defined"

pair, fst, snd :: Term
pair = error "To be defined"
fst = error "To be defined"
snd = error "To be defined"

-- Church numerals, page 60
c0, c1, c2, scc, plus :: Term
c0 = error "To be defined"
c1 = error "To be defined"
c2 = error "To be defined"
scc = error "To be defined"
plus = error "To be defined"

-- PRESERVATION, Theorem 9.3.9, on examples

-- All terms along the evaluation of a closed, well-typed term (obtained with
-- step) have the same type
preserves :: Term -> Bool
preserves = error "To be defined"

-- ERASURE, Definition 9.5.1 (uncomment together with the import above)

-- erase :: Term -> U.Term
-- erase = error "To be defined"
