{-|
Module      : Arithmetic Expressions
Description : Expressions, types, and operations on these

An Haskell adaptation of the code for Types and Programming Languages (TAPL), by
Benjamin Pierce, 2002, The MIT Press.

Fundamentals of Programming Languages
MSc on Informatics Engineering
Faculty of Sciences
University of Lisbon
2026/2027
-}

module Arithmetic where

import qualified Data.Set as Set

-- |Terms
data Term =
-- Figure 3.1, page 34
    TTrue
  | FFalse
  | If Term Term Term
-- Figure 3.2, page 41
  | Zero
  | Succ Term
  | Pred Term
  | IsZero Term
  | Max Term Term
-- Figure 3.2, page 41
-- TODO
  deriving
    ( Show
    , Eq, Ord) -- So that terms may go into Sets

-- 16
-- Type
data Type =
    BBool
  | NNat
  deriving (Show, Eq)

-- Some terms
s, t :: Term
s = If TTrue FFalse FFalse
t = If s TTrue TTrue
-- 13
-- t = if (if false then true else false) false else true
-- V = true
t13 = If (If FFalse TTrue FFalse) FFalse TTrue
-- 14
eval :: Term -> Term
eval t
  | t == TTrue = TTrue
  | t == FFalse = FFalse
  | t == Zero = Zero
  | otherwise = eval (step t)
-- 15
bigstep :: Term -> Term
-- B-Value
bigstep TTrue = TTrue
bigstep FFalse = FFalse
bigstep Zero = Zero
-- B-IfTrue B-IfFalse
bigstep (If t1 t2 t3) =
  case bigstep t1 of
    TTrue -> bigstep t2
    FFalse -> bigstep t3
    _ -> error "bigstep: condition must be a boolean"
-- B-Succ
bigstep (Succ t1) = Succ (bigstep t1)
-- B-PredZero B-PredSucc
bigstep (Pred t1) =
  case bigstep t1 of
    Zero -> Zero
    Succ nv -> nv
    _ -> error "bigstep: argument must be a natural number"
-- B-IsZeroZero B-IsZeroSucc
bigstep (IsZero t1) =
  case bigstep t1 of
    Zero -> TTrue
    Succ nv -> FFalse
    _ -> error "bigstep: argument must be a natural number"

-- 17
typeof :: Term -> Type
typeof TTrue = BBool
typeof FFalse = BBool
typeof Zero = NNat
typeof (If t1 t2 t3)  
  | typeof t1 == BBool
  , typeof t2 == typeof t3
  = typeof t2
typeof (Succ t1) 
  | typeof t1 == NNat
  = NNat
typeof (Pred t1) 
  | typeof t1 == NNat
  = NNat
typeof (IsZero t1) 
  | typeof t1 == NNat
  = BBool
typeof (Max t1 t2)
  | typeof t1 == NNat
  , typeof t2 == NNat 
  = NNat

isNumericValue :: Term -> Bool
isNumericValue Zero = True
isNumericValue (Succ t) = isNumericValue t
isNumericValue _ = False

-- |The set of constants appearing in a term, Definition 3.3.1, page 29
consts :: Term -> Set.Set Term
consts TTrue = Set.singleton TTrue
consts FFalse = Set.singleton FFalse
consts Zero = Set.singleton Zero
consts (If t1 t2 t3) = consts t1 `Set.union` consts t2 `Set.union` consts t3
-- 10
consts (Succ t1) = consts t1
consts (Pred t1) = consts t1
consts (IsZero t1) = consts t1

-- TODO: add arithmetic

-- Exercise: size, Definition 3.3.2, page 29

-- Exercise: depth, Definition 3.3.2, page 29

-- Exercise: width, see exercises-1-arithmetic.pdf

-- One-step evaluation
step :: Term -> Term
-- Figure 3.1, page 34
step (If TTrue t2 _) = t2
step (If FFalse _ t3) = t3
step (If t1 t2 t3) = If (step t1) t2 t3
-- Figure 3.2, page 41
-- E-Succ
step (Succ t1) = Succ (step t1)
-- E-PredZero
step (Pred Zero) = Zero
-- E-PredSucc
step (Pred (Succ nv)) = nv
-- E-Pred
step (Pred t1) = Pred (step t1)
-- E-IsZeroZero
step (IsZero Zero) = TTrue
-- E-IsZeroSucc
step (IsZero (Succ nv)) = FFalse
-- E-IsZero
step (IsZero t1) = IsZero (step t1)
-- 18
step (Max Zero Zero) = Zero
step (Max Zero (Succ nv2)) = Succ nv2
step (Max (Succ nv1) Zero) = Succ nv1
step (Max (Succ nv1) (Succ nv2)) = Succ (step (Max nv1 nv2))
step (Max t1 t2)
  | not (isNumericValue t1) =
      Max (step t1) t2
step (Max nv1 t2)
  | isNumericValue nv1 =
      Max nv1 (step t2)