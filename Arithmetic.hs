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
-- TODO
  deriving
    ( Show
    , Eq, Ord) -- So that terms may go into Sets

-- Some terms
s, t :: Term
s = If TTrue FFalse FFalse
t = If s TTrue TTrue

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
step (If TTrue t2 _) = t2
step (If FFalse _ t3) = t3
step (If t1 t2 t3) = If (step t1) t2 t3
-- Figure 3.2, page 41
-- TODO
