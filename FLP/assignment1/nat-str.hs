module Arithmetic where

import qualified Data.Set as Set

-- |Terms
data Term = 
      Zero
    | Succ Term
    | Term :+: Term
    | Epsilon
    | A Term
    | B Term
    | Len Term
    deriving
    ( Show
    , Eq, Ord) -- So that terms may go into Sets

-- A
-- Terms from 2.c
c1, c2, c3, c4, c5 :: Term
c1 = (Succ Zero) :+: (Succ Zero)
c2 = Succ (Zero :+: Succ (Zero))
c3 = Len (A (B Epsilon))
c4 = Succ (Len (B Epsilon))
c5 = (Len (A Epsilon)) :+: (Succ (Succ Zero))

-- B

isNv :: Term -> Bool
isNv Zero        = True
isNv (Succ e)    = isNv e
isNv _           = False 

isStr :: Term -> Bool
isStr Epsilon     = True
isStr (A e)       = isStr e
isStr (B e)       = isStr e
isStr _           = False

-- yields to True or False for every expression, if typable or not
val :: Term -> Bool
val e = isNv e || isStr e

-- One-step evaluation
step :: Term -> Term
step (Succ e1) = Succ (step e1)                 -- E-Succ
step (Zero :+: e2)
    | isNv e2 = e2                              -- E-PlusZero 
step (e1 :+: e2)
    | not (val e1) = step e1 :+: e2             -- E-PlusLeft   
    | isNv e1 && not (val e2) = e1 :+: step e2  -- E-PlusRight 
step (Succ e1 :+: e2)
    | isNv e1 && isNv e2 = Succ (e1 :+: e2)     -- E-PlusSucc
step (A e) = A (step e)                         -- E-A
step (B e) = B (step e)                         -- E-B
step (Len Epsilon) = Zero                       -- E-LenEmpty      
step (Len (A e))
    | isStr e = Succ (Len e)                    -- E-LenA
step (Len (B e))
    | isStr e = Succ (Len e)                    -- E-LenB
step (Len e)
    | not (val e) = Len (step e)                -- E-Len

eval :: Term -> Term
eval e
  | val e = e
  | otherwise = eval (step e)

-- C

-- verify if an expression is a normal form
normal :: Term -> Bool
normal Zero = True
normal (Succ e) = normal e              -- E-Succ
normal Epsilon = True
normal (A e) = normal e                 -- E-A
normal (B e) = normal e                 -- E-B
normal (Zero :+: e2) = not (isNv e2)    -- E-PlusZero
normal (Succ e1 :+: e2) 
    | isNv e1 = not (isNv e2)           -- E-PlusSucc
    | otherwise = normal e1
normal (e1 :+: e2) = normal e1          -- E-PlusLeft
normal (Len Epsilon) = False
normal (Len (A e)) 
    | isStr e = False                   -- E-LenA
    | otherwise = normal e
normal (Len (B e)) 
    | isStr e = False                   -- E-LenB
    | otherwise = normal e
normal (Len e) = normal e

valueIsNormal :: Term -> Bool
valueIsNormal e = normal e || not (val e)

-- D

data Type =
      NNat
    | SStr
    deriving (Show, Eq)

typeof :: Term -> Type
typeof Zero = NNat
typeof (Succ e1) 
  | typeof e1 == NNat
  = NNat
typeof (e1 :+: e2)
    | typeof e1 == NNat 
    , typeof e2 == NNat
    = NNat
typeof Epsilon = SStr
typeof (A e1)
    | typeof e1 == SStr
    = SStr
typeof (B e1)
    | typeof e1 == SStr
    = SStr  
typeof (Len e1)
    | typeof e1 == SStr
    = NNat

-- E

-- EXPRESSION:
-- succ ε

stuck :: Term
stuck = Succ Epsilon

-- normal stuck confirma que a expressão é uma normal form
-- val stuck confirma que a expressão não é um value
-- eval stuck dá erro, já que val e dá false, entra no otherwise e step não sabe como reduzir a expressão, disparando o erro
-- typeof stuck dá erro porque não está preparado para deduzir o tipo de um expressão do tipo Succ e, e: Str