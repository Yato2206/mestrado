module TypedLambda where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Prelude hiding (and, or, not, fst, snd)
-- Uncomment for the exercise on erasure; requires your module UntypedLambda
-- from Exercises 4
-- import qualified UntypedLambda as U

-- A

data Type =
    Nat               -- base type, Natural numbers
  | Arrow Type Type
  deriving Eq

instance Show Type where
  show Nat = "Nat"
  show (Arrow t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"

-- Names for variables
type Id = String

data Term =
-- Figure 9-1, page 103
    Var Id
  | Abs Id Type Term
  | App Term Term
  | Zero
  | Succ Term
  | Rec Term Id Id Term Term -- t0 x y t1 t2 = rec(t0; x.y.t1) (t2)

instance Show Term where
  show (Var x) = x
  show (Abs x u t) = "(\\" ++ x ++ ":" ++ show u ++ "." ++ show t ++ ")" -- λ = \
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show Zero = "0"
  show (Succ t) = "succ " ++ show t
  show (Rec t0 x y t1 t2) = 
    "rec(" ++ show t0 ++ "; " ++ x ++ "." ++ y ++ "." ++ show t1 ++ ")(" ++ show t2 ++ ")"

-- Números de 1 a 4
one, two, three, four :: Term
one = Succ Zero
two = Succ one
three = Succ two
four = Succ three

-- double = λn:Nat. rec(0; x.y.succ(succ y))(n)
double, doubleTwo, ssum, ssumTwoFour :: Term
double = Abs "n" Nat (Rec Zero "x" "y" (Succ (Succ (Var "y"))) (Var "n"))

doubleTwo = App double two

-- sum = λn:Nat.λm:Nat. rec(m; x.y.succ y)(n)
ssum = Abs "n" Nat (Abs "m" Nat (Rec (Var "m") "x" "y" (Succ (Var "y")) (Var "n")))

ssumTwoFour = App (App ssum two) four

-- B
-- TYPING

type Context = Map.Map Id Type

typeof :: Context -> Term -> Type
typeof ctx (Var x) = 
    case Map.lookup x ctx of
        Just ty -> ty
        Nothing -> error ("unbounded variable: " ++ x)
typeof ctx (Abs x ty1 t) = 
    let ty2 = typeof (Map.insert x ty1 ctx) t
    in Arrow ty1 ty2
typeof ctx (App t1 t2) =
    case typeof ctx t1 of
        Arrow ty11 ty12
            | typeof ctx t2 == ty11 -> ty12
            | otherwise -> error "parameter type mismatch"
        _ -> error "arrow type expected"
-- Godel's System T additions
typeof ctx Zero = Nat
typeof ctx (Succ t1)
    | typeof ctx t1 == Nat = Nat
    | otherwise = error "argument of succ is not a Nat"
typeof ctx (Rec t0 x y t1 t2)
    | typeof ctx t2 /= Nat = error "argument of rec is not a Nat"
    | otherwise =
        let ty = typeof ctx t0
            ctx' = Map.insert y ty (Map.insert x Nat ctx)
            ty1 = typeof ctx' t1
        in if ty1 == ty
            then ty
            else error "step case of rec does not match base case type"

-- typeof Map.empty double: Nat -> Nat (igual ao 1.D)
-- typeof Map.empty doubleTwo: Nat (igual ao 1.D)
-- typeof Map.empty sum: Nat -> (Nat -> Nat) (igual ao 1.D)
-- typeof Map.empty sumTwoFour: Nat (igual ao 1.D)

-- C

-- The free variables of an expression
freeVars :: Term -> Set.Set Id
freeVars (Var x)       = Set.singleton x
freeVars (Abs x _ t1)  = Set.delete x (freeVars t1)
freeVars (App t1 t2)   = freeVars t1 `Set.union` freeVars t2
freeVars (Zero)        = Set.empty
freeVars (Succ t1)     = freeVars t1
freeVars (Rec t0 x y t1 t2) = 
    freeVars t0 `Set.union` (Set.delete x (Set.delete y (freeVars t1))) `Set.union` freeVars t2

-- [x -> s]t. Substitution, as in TAPL, def 5.3.5, page 71, but with on-the-fly
-- renaming when y in freeVars(s) and x in freeVars(t)
subs :: Id -> Term -> Term -> Term
subs x s (Var y)
  | y == x    = s
  | otherwise = Var y
subs x s (Abs y τ t)
  -- Optimise
  | x == y = Abs y τ t
  | y `Set.notMember` fvS || x `Set.notMember` fvT = Abs y τ (subs x s t)
  | otherwise = Abs z τ (subs x s (subs y (Var z) t))
  where fvS = freeVars s
        fvT = freeVars t
        z = newId (fvS `Set.union` fvT)
subs x s (App t1 t2) = App (subs x s t1) (subs x s t2)
subs x s Zero = Zero
subs x s (Succ t1) = Succ (subs x s t1)
subs x s (Rec t0 vx vy t1 t2) =
  case subs x s (Abs vx Nat (Abs vy Nat t1)) of
    Abs vx' _ (Abs vy' _ t1') -> Rec (subs x s t0) vx' vy' t1' (subs x s t2)

-- A fresh variable name that is, a variable name that is not present in a set
-- of variables
newId :: Set.Set Id -> Id
newId vs = head [v | n <- [0..], let v = '_':show n, v `Set.notMember` vs]

-- values
value :: Term -> Bool
-- Figure 9-1, page 103
value Abs{} = True
value Zero = True 
value (Succ t) = value t
value _ = False

-- single-step evaluator
-- Partial: undefined on values and on variables (no rule applies)
step :: Term -> Term
-- Figure 9-1, page 103
step (App (Abs x _ t1) v2) | value v2 = subs x v2 t1      -- E-AppAbs
step (App v1 t2)           | value v1 = App v1 (step t2) -- E-App2
step (App t1 t2)                      = App (step t1) t2 -- E-App1
step (Succ t1)                        = Succ (step t1)   -- E-Succ
step (Rec t0 x y t1 Zero)             = t0                 -- E-RecZ
step (Rec t0 x y t1 (Succ nv)) | isNv nv =
  subs y (Rec t0 x y t1 nv) (subs x nv t1)                 -- E-RecS
step (Rec t0 x y t1 t2)               = Rec t0 x y t1 (step t2)  -- E-RecA

-- numeric-value check, needed for E-RecS's guard
isNv :: Term -> Bool
isNv Zero = True
isNv (Succ t) = isNv t
isNv _ = False

-- multi-step evaluator
-- Precondition: t is closed and well typed (in the empty context), so that,
-- by progress, t is either a value or else it takes a step
eval :: Term -> Term
eval t
  | value t = t
  | otherwise = eval (step t)

-- eval doubleTwo: succ succ succ succ 0 (4) -- resultado espectado
-- eval sumTwoFour: succ succ succ succ succ succ 0 (6) -- resultado espectado

-- D

ppred, times, fact :: Term

-- pred = λn:Nat. rec(0; x.y.x)(n)
ppred = Abs "n" Nat (Rec Zero "x" "y" (Var "x") (Var "n"))
-- typeof Map.empty ppred = Nat -> Nat

-- times = λn:Nat.λm:Nat. rec(0; x.y. sum y m)(n)
times = Abs "n" Nat (Abs "m" Nat (Rec Zero "x" "y" (App (App ssum (Var "y")) (Var "m")) (Var "n")))
-- typeof Map.empty times = Nat -> (Nat -> Nat)

-- fact = λn:Nat. rec(1; x.y. times (succ x) y)(n)
fact = Abs "n" Nat (Rec one "x" "y" (App (App times (Succ (Var "x"))) (Var "y")) (Var "n"))
-- typeof Map.empty fact = Nat -> Nat

-- E
 
-- ack = λm:Nat. rec(λn:Nat.succ n; x.x'. λn:Nat. rec(x' 1; y.y'. x' y')(n))(m)
ack :: Term
ack = Abs "m" Nat (Rec (Abs "n" Nat (Succ (Var "n"))) "x" "x'" (Abs "n" Nat (
  Rec (App (Var "x'") one) "y" "y'" (App (Var "x'") (Var "y'")) (Var "n"))) (Var "m"))
-- typeof Map.empty ack = Nat -> (Nat -> Nat) igual ao tipo obtido em 1.F e igual ao tipo que está no enunciado da questão (correto)

ackOneTwo, ackTwoTwo :: Term
ackOneTwo = App (App ack one) two
-- eval ackOneTwo  = succ succ succ succ 0 (4) (como está no enunciado)

ackTwoTwo = App (App ack two) two
-- eval ackTwoTwo  = succ succ succ succ succ succ succ 0 (7) (como está no enunciado)