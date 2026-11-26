{-|
Module      : The simply typed lambda-calculus with booleans and numbers
Description : Terms, substitution, evaluation, types, typing.

A Haskell adaptation of the code for Types and Programming Languages (TAPL), by
Benjamin Pierce, 2002, The MIT Press.

Fundamentals of Programming Languages
MSc in Informatics Engineering
Faculty of Sciences
University of Lisbon
2026/27
-}

module Extensions where

import qualified Data.Set as Set
import qualified Data.Map as Map

data Type =
-- Figure 8-1, page 93
    BBool
-- Figure 8-2, page 93
  | Nat
-- Figure 9-1, page 103
  | Arrow Type Type
  deriving Eq

instance Show Type where
  show BBool = "Bool"
  show Nat = "Nat"
  show (Arrow t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"

-- Names for variables
type Id = String

data Term =
-- Figure 3-1, page 34
    TTrue
  | FFalse
  | If Term Term Term
-- Figure 3-2, page 41
  | Zero
  | Succ Term
  | Pred Term
  | IsZero Term
-- Figure 9-1, page 103
  | Var Id
  | Abs Id Type Term
  | App Term Term

instance Show Term where
  show TTrue = "true"
  show FFalse = "false"
  show (If t1 t2 t3) = "(if " ++ show t1 ++ " then " ++ show t2 ++ " else " ++ show t3 ++ ")"
  show Zero = "0"
  show (Succ t1) = "(succ " ++ show t1 ++ ")"
  show (Pred t1) = "(pred " ++ show t1 ++ ")"
  show (IsZero t1) = "(iszero " ++ show t1 ++ ")"
  show (Var x) = x
  show (Abs x u t) = "(λ" ++ x ++ ":" ++ show u ++ "." ++ show t ++ ")"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"

-- The free variables of a term
freeVars :: Term -> Set.Set Id
-- Figure 3-1, page 34
freeVars TTrue         = Set.empty
freeVars FFalse        = Set.empty
freeVars (If t1 t2 t3) = freeVars t1 `Set.union` freeVars t2 `Set.union` freeVars t3
-- Figure 3-2, page 41
freeVars Zero          = Set.empty
freeVars (Succ t1)     = freeVars t1
freeVars (Pred t1)     = freeVars t1
freeVars (IsZero t1)   = freeVars t1
-- Figure 9-1, page 103
freeVars (Var x)       = Set.singleton x
freeVars (Abs x _ t1)  = Set.delete x (freeVars t1)
freeVars (App t1 t2)   = freeVars t1 `Set.union` freeVars t2

-- [x -> s]t. Substitution, as in TAPL, def 5.3.5, page 71, but with on-the-fly
-- renaming when y in freeVars(s) and x in freeVars(t)
subs :: Id -> Term -> Term -> Term
-- Figure 3-1, page 34
subs _ _ TTrue         = TTrue
subs _ _ FFalse        = FFalse
subs x s (If t1 t2 t3) = If (subs x s t1) (subs x s t2) (subs x s t3)
-- Figure 3-2, page 41
subs _ _ Zero          = Zero
subs x s (Succ t1)     = Succ (subs x s t1)
subs x s (Pred t1)     = Pred (subs x s t1)
subs x s (IsZero t1)   = IsZero (subs x s t1)
-- Figure 9-1, page 103
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

-- Numeric values, Figure 3-2, page 41
numericValue :: Term -> Bool
numericValue Zero = True
numericValue (Succ nv) = numericValue nv
numericValue _ = False

-- Values
value :: Term -> Bool
-- Figure 3-1, page 34
value TTrue = True
value FFalse = True
-- Figure 9-1, page 103
value Abs{} = True
-- Figure 3-2, page 41
value t = numericValue t

-- Single-step evaluator
-- Partial: undefined on values and on stuck terms (no rule applies)
step :: Term -> Term
-- Figure 3-1, page 34
step (If TTrue t2 _)  = t2                                  -- E-IfTrue
step (If FFalse _ t3) = t3                                  -- E-IfFalse
step (If t1 t2 t3)    = If (step t1) t2 t3                  -- E-If
-- Figure 3-2, page 41
step (Succ t1)                           = Succ (step t1)   -- E-Succ
step (Pred Zero)                         = Zero             -- E-PredZero
step (Pred (Succ nv1)) | numericValue nv1 = nv1             -- E-PredSucc
step (Pred t1)                           = Pred (step t1)   -- E-Pred
step (IsZero Zero)                       = TTrue            -- E-IszeroZero
step (IsZero (Succ nv1)) | numericValue nv1 = FFalse        -- E-IszeroSucc
step (IsZero t1)                         = IsZero (step t1) -- E-IsZero
-- Figure 9-1, page 103
step (App (Abs x _ t1) v2) | value v2 = subs x v2 t1        -- E-AppAbs
step (App v1 t2)           | value v1 = App v1 (step t2)    -- E-App2
step (App t1 t2)                      = App (step t1) t2    -- E-App1

-- Multi-step evaluator
-- Precondition: t is closed and well typed (in the empty context), so that,
-- by progress, t is either a value or else it takes a step
eval :: Term -> Term
eval t
  | value t = t
  | otherwise = eval (step t)

-- TYPING

type Context = Map.Map Id Type

-- Partial: undefined on terms that are not typable
typeof :: Context -> Term -> Type
-- Figure 8-1, page 93
typeof _ TTrue = BBool
typeof _ FFalse = BBool
typeof ctx (If t1 t2 t3) | τ1 == BBool && τ2 == τ3 = τ2
  where τ1 = typeof ctx t1
        τ2 = typeof ctx t2
        τ3 = typeof ctx t3
-- Figure 8-2, page 93
typeof _ Zero = Nat
typeof ctx (Succ t1)   | typeof ctx t1 == Nat = Nat
typeof ctx (Pred t1)   | typeof ctx t1 == Nat = Nat
typeof ctx (IsZero t1) | typeof ctx t1 == Nat = BBool
-- Figure 9-1, page 103
typeof ctx (Var x) = ctx Map.! x
typeof ctx (Abs x τ1 t2) = Arrow τ1 τ2
  where τ2 = typeof (Map.insert x τ1 ctx) t2
typeof ctx (App t1 t2) | τ11 == τ11' = τ12
  where Arrow τ11 τ12 = typeof ctx t1
        τ11' = typeof ctx t2
