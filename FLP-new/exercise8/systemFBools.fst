{- |
System F booleans in FreeST

Fundamentals of Programming Languages
MSc in Informatics Engineering
Faculty of Sciences, University of Lisbon
2026/2027
Vasco T. Vasconcelos

Church encoding of the boolean values, after TAPL, Section 23.4.

Run with: freest systemFBools.fst

Type variables are annotated with kind *T (unrestricted types): without it,
FreeST takes their values to be linear, to be used exactly once, and rejects
functions that discard or copy them.
-}

-- 1. The type of Church booleans: a boolean chooses between two alternatives

type CBool = forall (a:*T) -> a -> a -> a

-- 2. The values and the operations, as in TAPL

cTrue : CBool
cTrue = \@(a:*T) (t:a) (f:a) -> t

cFalse : CBool
cFalse = \@(a:*T) (t:a) (f:a) -> f

cNot : CBool -> CBool
cNot = \(b:CBool) -> \@(a:*T) (t:a) (f:a) -> b @a f t

cAnd : CBool -> CBool -> CBool
cAnd = \(b:CBool) (c:CBool) -> b @CBool c cFalse

cOr : CBool -> CBool -> CBool
cOr = \(b:CBool) (c:CBool) -> b @CBool cTrue c

-- 3. From Church booleans to FreeST booleans.

toBool : CBool -> Bool
toBool b = b @Bool True False

-- Expect: True
_ = print (toBool $ cAnd (cOr cFalse cTrue) (cNot cFalse))
