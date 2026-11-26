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
  | Zero
  | Succ Term
  | Pred Term
  | IsZero Term
-- Figure 3.2, page 41
-- TODO
  deriving
    ( Show
    , Eq, Ord) -- So that terms may go into Sets

-- Some terms
s, t :: Term
s = If TTrue FFalse FFalse
t = If s TTrue TTrue

-- Naturals
one, two, three, four, five :: Term
one = Succ Zero
two = Succ (Succ Zero)
three = Succ (Succ (Succ Zero))
four = Succ (Succ (Succ (Succ Zero)))
five = Succ (Succ (Succ (Succ (Succ Zero))))

-- Two or more conditionals
twoC, threeC, fourC, fiveC :: Term
twoC = If TTrue (If FFalse TTrue FFalse) TTrue
threeC = If TTrue (If FFalse TTrue FFalse) (If TTrue FFalse TTrue)
fourC = If TTrue (If FFalse TTrue (If TTrue FFalse TTrue)) (If FFalse TTrue FFalse)
fiveC = If TTrue (If FFalse TTrue (If TTrue FFalse (If FFalse TTrue (If TTrue FFalse TTrue)))) FFalse

-- Mix arithmetic and boolean
example :: Term
example = If (IsZero (Succ Zero)) TTrue FFalse

notT :: Term -> Term
notT t1 = If t1 FFalse TTrue

orR :: Term -> Term
orR t1 t2 = If t1 TTrue t2

andD :: Term -> Term
andD t1 t2 = If t1 t2 FFalse

isoneE :: Term -> Term
isoneE t1 = If (IsZero t1) FFalse (IsZero (pred t1))

gzZ :: Term -> Term
gzZ t1 = If (IsZero t1) FFalse TTrue

-- Expressions from item 4
-- Evaluate
f1, f2, f3, f4, f5, f6, f7 :: Term
f1 = Pred (Succ Zero)
f2 = IsZero (Pred (Succ Zero))
f3 = Succ (Pred Zero)
f4 = Succ (Pred (Succ Zero))
-- Don't evaluate
f5 = Succ (FFalse) 
f6 = Pred (TTrue)
f7 = Pred (IsZero (Zero))

-- |The set of constants appearing in a term, Definition 3.3.1, page 29
consts :: Term -> Set.Set Term
consts TTrue = Set.singleton TTrue
consts FFalse = Set.singleton FFalse
consts (If t1 t2 t3) = consts t1 `Set.union` consts t2 `Set.union` consts t3
-- TODO: add arithmetic

-- Exercise: size, Definition 3.3.2, page 29

-- Exercise: depth, Definition 3.3.2, page 29

-- Exercise: width, see exercises-1-arithmetic.pdf

-- One-step evaluation
step :: Term -> Term
-- Figure 3.1, page 34
--step (If TTrue t2 _) = t2
--step (If FFalse _ t3) = t3
--step (If t1 t2 t3) = If (step t1) t2 t3
-- Arithmetic rules
--step (Pred Zero) = Zero
--step (Pred (Succ nv)) = nv
--step (Pred t1) = Pred (step t1)
--step (Succ t1) = Succ (step t1)

--step (IsZero Zero) = TTrue
--step (IsZero (Succ nv)) = FFalse
--step (IsZero t1) = IsZero (step t1)
--Dont Evaluate
--step (f5)
--step (f6)
--step (f7)

-- Figure 3.2, page 41
-- TODO
-- Exercise: size, Definition 3.3.2, page 29
size :: Term -> Int
size TTrue = 1
size FFalse = 1
size Zero = 1
size (Succ t) = size t + 1
size (Pred t) = size t + 1
size (IsZero t) = size t + 1
size (If t1 t2 t3) size t1 + size t2 + size t3 + 1

-- Exercise: depth, Definition 3.3.2, page 29

depth :: Term -> Int
depth TTrue = 1
depth FFalse = 1
depth Zero = 1
depth (Succ t) = depth t + 1
depth (Pred t) = depth t + 1
depth (IsZero t) = depth t + 1
depth (If t1 t2 t3) = max (depths t1) (max (depths t2) (depths t3)) + 1

-- Exercise: width, see exercises-1-arithmetic.pdf

width :: Term -> Int
width TTrue = 1
width FFalse = 1
width Zero = 1
width (Succ t) = width t
width (Pred t) = width t
width (IsZero t) = width t
width (If t1 t2 t3) = width t1 + width t2 + width t3

-- One-step evaluation
step :: Term -> Term
-- Figure 3.1, page 34
step (If TTrue t2 _) = t2
step (If FFalse _ t3) = t3
step (If t1 t2 t3) = If (step t1) t2 t3
-- Figure 3.2, page 41
step (Succ t1) = Succ(step t1)
step (Pred Zero) = Zero
step (Pred(Succ t1)) = t1
step (Pred t1) = Pred(step t1)
step (IsZero Zero) = TTrue
step (IsZero (Succ t1)) = FFalse
step (IsZero t1) = IsZero(step t1)