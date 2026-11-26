module Records where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List (intercalate)

-- A

type Id = String
type Label = String

-- {} (the empty record type) plays the role of the base type.
-- Records are ordered: a list of (label, _) pairs. Distinct labels are
-- checked by typeof (part B), not by the datatypes.
data Type =
    Arrow Type Type
  | TRcd [(Label, Type)]
  deriving Eq

data Pattern =
    PVar Id
  | PRcd [(Label, Pattern)]

data Term =
    Var Id
  | Abs Id Type Term
  | App Term Term
  | Rcd [(Label, Term)]
  | Proj Term Label
  | Let Pattern Term Term      -- let p = t1 in t2

instance Show Type where
  show (Arrow t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TRcd fs) = "{" ++ intercalate ", " [l ++ " : " ++ show t | (l, t) <- fs] ++ "}"

instance Show Pattern where
  show (PVar x) = x
  show (PRcd ps) = "{" ++ intercalate ", " [l ++ " = " ++ show p | (l, p) <- ps] ++ "}"

instance Show Term where
  show (Var x) = x
  show (Abs x u t) = "(\\" ++ x ++ ":" ++ show u ++ "." ++ show t ++ ")"
  show (App t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
  show (Rcd fs) = "{" ++ intercalate ", " [l ++ " = " ++ show t | (l, t) <- fs] ++ "}"
  show (Proj t l) = show t ++ "." ++ l
  show (Let p t1 t2) = "(let " ++ show p ++ " = " ++ show t1 ++ " in " ++ show t2 ++ ")"

-- Variables bound by a pattern (with repetitions, if any)
patVars :: Pattern -> [Id]
patVars (PVar x) = [x]
patVars (PRcd ps) = concatMap (patVars . snd) ps

-- The free variables of a term
freeVars :: Term -> Set.Set Id
freeVars (Var x)       = Set.singleton x
freeVars (Abs x _ t1)  = Set.delete x (freeVars t1)
freeVars (App t1 t2)   = freeVars t1 `Set.union` freeVars t2
freeVars (Rcd fs)      = Set.unions [freeVars t | (_, t) <- fs]
freeVars (Proj t _)    = freeVars t
freeVars (Let p t1 t2) =
  freeVars t1 `Set.union` (freeVars t2 `Set.difference` Set.fromList (patVars p))

newId :: Set.Set Id -> Id
newId vs = head [v | n <- [0 :: Int ..], let v = '_' : show n, v `Set.notMember` vs]

-- [x -> s]t, with on-the-fly renaming of bound variables to avoid capture
subs :: Id -> Term -> Term -> Term
subs x s (Var y)
  | y == x    = s
  | otherwise = Var y
subs x s (Abs y ty t)
  | x == y = Abs y ty t
  | y `Set.notMember` fvS || x `Set.notMember` fvT = Abs y ty (subs x s t)
  | otherwise = Abs z ty (subs x s (subs y (Var z) t))
  where fvS = freeVars s
        fvT = freeVars t
        z = newId (fvS `Set.union` fvT)
subs x s (App t1 t2) = App (subs x s t1) (subs x s t2)
subs x s (Rcd fs) = Rcd [(l, subs x s t) | (l, t) <- fs]
subs x s (Proj t l) = Proj (subs x s t) l
subs x s (Let p t1 t2)
  | x `elem` patVars p = Let p (subs x s t1) t2
  | otherwise          = Let p (subs x s t1) (subs x s t2)

-- values
value :: Term -> Bool
value Abs{}    = True
value (Rcd fs) = all (value . snd) fs
value _        = False

-- match p v (Figure 11-8): the substitution, or Nothing if v does not match.
-- M-Rcd: same labels, in the same order.
match :: Pattern -> Term -> Maybe [(Id, Term)]
match (PVar x) v = Just [(x, v)]                          -- M-Var
match (PRcd []) (Rcd []) = Just []                        -- M-Empty
match (PRcd ((l, p) : ps)) (Rcd ((l', t) : fs))           -- M-Rcd
  | l == l' = do
      s1 <- match p t
      s2 <- match (PRcd ps) (Rcd fs)
      return (s1 ++ s2)
match _ _ = Nothing

-- Applies the substitution one variable at a time. Fine for closed values,
-- which is all that evaluation of closed terms produces.
applySubst :: [(Id, Term)] -> Term -> Term
applySubst s t = foldr (\(x, v) acc -> subs x v acc) t s

-- single-step evaluator
-- Partial: undefined on values and on variables (no rule applies)
step :: Term -> Term
step (App (Abs x _ t1) v2) | value v2 = subs x v2 t1             -- E-AppAbs
step (App v1 t2)           | value v1 = App v1 (step t2)         -- E-App2
step (App t1 t2)                      = App (step t1) t2         -- E-App1
step (Rcd fs) =                                                  -- E-Rcd
  case break (not . value . snd) fs of
    (vs, (l, t) : rest) -> Rcd (vs ++ (l, step t) : rest)
    _                   -> error "step: record is a value"
step (Proj t l)
  | value t   = project t l                                      -- E-ProjRcd
  | otherwise = Proj (step t) l                                  -- E-Proj
step (Let p v t2) | value v =                                    -- E-LetV
  case match p v of
    Just s  -> applySubst s t2
    Nothing -> error "step: pattern does not match"
step (Let p t1 t2) = Let p (step t1) t2                          -- E-Let

-- the field l of a record value
project :: Term -> Label -> Term
project (Rcd fs) l =
  case lookup l fs of
    Just t  -> t
    Nothing -> error ("step: no field " ++ l)
project _ _ = error "step: record expected"

-- multi-step evaluator; precondition: t closed and well typed
eval :: Term -> Term
eval t
  | value t   = t
  | otherwise = eval (step t)

-- B
-- Typing. Rules of the language, with the T-LetP of TAPL (Figure 11-8):
--
--   Gamma |- t1 : T1     |- p : T1 => Delta     Gamma, Delta |- t2 : T2
--   -------------------------------------------------------------------
--                    Gamma |- let p = t1 in t2 : T2

type Context = Map.Map Id Type
 
 
-- True if a list has repeated elements
hasDup :: Ord a => [a] -> Bool
hasDup xs = Set.size (Set.fromList xs) /= length xs
 
-- Pattern typing  |- p : T => Delta  (TAPL Figure 11-8): the bindings of p's
-- variables. The labels must be the same, in the same order, as in the type.
patBinds :: Pattern -> Type -> [(Id, Type)]
patBinds (PVar x) ty = [(x, ty)]                       -- PT-Var
patBinds (PRcd []) (TRcd []) = []                      -- PT-Empty
patBinds (PRcd ((l, p) : ps)) (TRcd ((l', ty) : fs))   -- PT-Rcd
  | l == l' = patBinds p ty ++ patBinds (PRcd ps) (TRcd fs)
patBinds _ _ = error "pattern does not match the type"
 
typeof :: Context -> Term -> Type
-- T-Var
typeof ctx (Var x) =
  case Map.lookup x ctx of
    Just ty -> ty
    Nothing -> error ("unbound variable: " ++ x)
-- T-Abs
typeof ctx (Abs x ty1 t) = Arrow ty1 (typeof (Map.insert x ty1 ctx) t)
-- T-App
typeof ctx (App t1 t2) =
  case typeof ctx t1 of
    Arrow ty11 ty12
      | typeof ctx t2 == ty11 -> ty12
      | otherwise             -> error "parameter type mismatch"
    _ -> error "arrow type expected"
-- T-RcdEmpty and T-Rcd: the labels of a record must be distinct
typeof ctx (Rcd fs)
  | hasDup (map fst fs) = error "duplicate labels in record"
  | otherwise           = TRcd [(l, typeof ctx t) | (l, t) <- fs]
-- T-Proj
typeof ctx (Proj t l) =
  case typeof ctx t of
    TRcd fs -> case lookup l fs of
                 Just ty -> ty
                 Nothing -> error ("no field " ++ l)
    _ -> error "record type expected"
-- T-LetP
typeof ctx (Let p t1 t2)
  | hasDup (patVars p) = error "pattern binds a variable more than once"
  | otherwise =
      let delta = Map.fromList (patBinds p (typeof ctx t1))
      in typeof (Map.union delta ctx) t2

-- C
tU :: Type
tU = TRcd []

-- ThreeSeq = {foo : {}, bar : {foo : {}, bar : {}}}
threeSeq :: Type
threeSeq = TRcd [("foo", tU), ("bar", TRcd [("foo", tU), ("bar", tU)])]
 
-- SixSeq = {foo : ThreeSeq, bar : ThreeSeq}
sixSeq :: Type
sixSeq = TRcd [("foo", threeSeq), ("bar", threeSeq)]

-- helpers: the term {foo = x, bar = {foo = y, bar = z}} and the pattern for it
seq3 :: Term -> Term -> Term -> Term
seq3 x y z = Rcd [("foo", x), ("bar", Rcd [("foo", y), ("bar", z)])]
 
pat3 :: Id -> Id -> Id -> Pattern
pat3 x y z = PRcd [("foo", PVar x), ("bar", PRcd [("foo", PVar y), ("bar", PVar z)])]
 
-- mk : {} -> {} -> {} -> ThreeSeq
mk :: Term
mk = Abs "a" tU (Abs "b" tU (Abs "c" tU (seq3 (Var "a") (Var "b") (Var "c"))))
 
-- append : ThreeSeq -> ThreeSeq -> SixSeq
append :: Term
append =
  Abs "s1" threeSeq (Abs "s2" threeSeq
    (Let (pat3 "a" "b" "c") (Var "s1")
      (Let (pat3 "d" "e" "f") (Var "s2")
        (Rcd [ ("foo", seq3 (Var "a") (Var "b") (Var "c"))
             , ("bar", seq3 (Var "d") (Var "e") (Var "f")) ]))))

-- Checking the types with typeof
-- typeof Map.empty mk = ({} -> ({} -> ({} -> ThreeSeq))) ou ({} -> ({} -> ({} -> {foo : {}, bar : {foo : {}, bar : {}}})))
-- typeof Map.empty append = (ThreeSeq -> (ThreeSeq -> SixSeq)) ou ({foo : {}, bar : {foo : {}, bar : {}}} -> ({foo : {}, bar : {foo : {}, bar : {}}} -> {foo : {foo : {}, bar : {foo : {}, bar : {}}}, bar : {foo : {}, bar : {foo : {}, bar : {}}}}))

mkOk, appendOk :: Bool
-- Checking if the types are as expected. The following should be True:
mkOk     = typeof Map.empty mk == Arrow tU (Arrow tU (Arrow tU threeSeq))
appendOk = typeof Map.empty append == Arrow threeSeq (Arrow threeSeq sixSeq)
 
unit :: Term
unit = Rcd []
 
idf :: Term
idf = Abs "x" tU (Var "x")
 
-- Two sequences built with mk (the second one has a field that must be
-- evaluated: {} is the only value of type {}, so this is how we see evaluation)
mkUnit, mkUnit2 :: Term
mkUnit  = App (App (App mk unit) unit) unit
mkUnit2 = App (App (App mk (App idf unit)) unit) unit
 
-- append (mk {} {} {}) (mk (idf {}) {} {})
appendTest :: Term
appendTest = App (App append mkUnit) mkUnit2
 
-- typeof Map.empty appendTest == sixSeq (verified as true)
-- eval appendTest = (a value of type sixSeq)
--   {foo = {foo = {}, bar = {foo = {}, bar = {}}},
--    bar = {foo = {}, bar = {foo = {}, bar = {}}}} 

-- D
-- For a closed well-typed t: every term along the evaluation of t has the type
-- of t (preservation), and the last one is a value (progress: no stuck term).

-- go walks the evaluation of t. ty, the type of the ORIGINAL term, is fixed
-- in the where, so every later term is compared with it (preservation).
-- Calling safe recursively would recompute the type from the current term.
safe :: Term -> Bool
safe t = go t
  where
    ty = typeof Map.empty t
    go u
      | typeof Map.empty u /= ty = False          -- preservation fails
      | value u                  = True           -- ended in a value
      | otherwise = go (step u)

-- Terms for safe (all closed and well typed)
safeTests :: [(String, Term)]
safeTests =
  [ ("mk applied",      mkUnit)
  , ("append applied",  appendTest)
  , ("let in lambda",   App (Abs "r" (TRcd [("foo", tU)])
                              (Let (PRcd [("foo", PVar "u")]) (Var "r") (Var "u")))
                            (Rcd [("foo", App idf unit)]))

  -- projection after evaluating a field: {foo = idf {}, bar = idf}.bar
  , ("proj", Proj (Rcd [("foo", App idf unit), ("bar", idf)]) "bar")

  -- E-Rcd, left to right: both fields need several steps
  , ("rcd order", Rcd [("foo", App idf unit), ("bar", App idf (App idf unit))])

  -- nested pattern, with a non-value on the right: E-Let steps it first
  , ("nested let", Let (pat3 "x" "y" "z") (seq3 unit idf (App idf unit))
                            (Rcd [("foo", Var "z"), ("bar", App (Var "y") (Var "x"))]))

  -- higher-order: a function that receives a function
  , ("higher-order", App (Abs "f" (Arrow tU tU) (App (Var "f") unit)) idf)

  -- shadowing: the inner x hides the outer one
  , ("shadowing", Let (PVar "x") unit (Let (PVar "x") idf (App (Var "x") unit)))
  ]
 
-- Command to run: map (\(n, t) -> (n, safe t)) safeTests -> all tests should give true

-- E
-- Not every type computed by typeof is well formed (same answer as 1.G):
-- badTerm below is a counterexample.
-- Proof: typeof only rejects repeated labels in record TERMS (case Rcd). In the
-- case of Abs it copies the annotation ty1 to the result without checking it,
-- so the annotation of badTerm enters the computed type, which is not well formed.


-- A type is well formed if the labels of each record type in it are distinct.
wellFormed :: Type -> Bool
wellFormed (Arrow t1 t2) = wellFormed t1 && wellFormed t2
wellFormed (TRcd fs)     = not (hasDup (map fst fs)) && all (wellFormed . snd) fs
 
-- Countraexemple:
-- \x:{foo:{}, foo:{}}. x
badTerm :: Term
badTerm = Abs "x" (TRcd [("foo", tU), ("foo", tU)]) (Var "x")
 
-- typeof Map.empty badTerm = ({foo : {}, foo : {}} -> {foo : {}, foo : {}})
-- wellFormed (typeof Map.empty badTerm) = False

-- Igual a 1.G: lá, derivable-not-wf dá o mesmo termo, porque T-Abs também não verifica
-- a anotação; a correção é a mesma (premissa wf T1 em T-Abs).