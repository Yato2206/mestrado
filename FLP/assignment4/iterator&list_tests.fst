-- 7
type Nat = forall (c:*T) -> c -> (c -> c) -> c

-- zero := λX. λs: X -> X. λz: X . z
zero : Nat
zero @c z s = z

-- succ := λn:CNat. λX. λs: X -> X. λz:X . s (n [X] s z)
succ' : Nat -> Nat
succ' n = \@(c:*T) (z:c) (s:c -> c) -> s (n @c z s)

-- Tests (depois apagar)
_ = print "=============TESTS EXERCISE 7=============="
 
_ = print (zero @Int 0 (\(n:Int) -> n + 1))                       -- expected: 0
_ = print (succ' zero @Int 0 (\(n:Int) -> n + 1))                 -- expected: 1
_ = print (succ' (succ' zero) @Int 0 (\(n:Int) -> n + 1))         -- expected: 2
_ = print (succ' (succ' (succ' zero)) @Int 0 (\(n:Int) -> n + 1)) -- expected: 3
 
-- the result type c can change (here String)
_ = putStrLn (succ' (succ' zero) @String "z" (\(x:String) -> "s(" ++ x ++ ")")) -- expected: s(s(z))

-- 8

-- iter = Λc. λn: Nat. λz: c. λs: c -> c. n [c] s z
iter : forall (c:*T) -> Nat -> c -> (c -> c) -> c
iter @c n z s = n @c z s

-- Tests (depois apagar)
_ = print "=============TESTS EXERCISE 8=============="
 
three' : Nat
three' = succ' (succ' (succ' zero))
 
_ = print (iter @Int zero 0 (\(n:Int) -> n + 1))    -- expected: 0
_ = print (iter @Int three' 0 (\(n:Int) -> n + 1))  -- expected: 3
_ = print (iter @Int three' 1 (\(n:Int) -> n * 2))  -- expected: 8
 
-- with zero as the base, the step is not applied
_ = print (iter @Int zero 42 (\(n:Int) -> n * 2))  -- expected: 42
 
-- the result type c can change (here String)
_ = putStrLn (iter @String three' "z" (\(x:String) -> "s(" ++ x ++ ")")) -- expected: s(s(s(z)))
 
 -- 9

-- plus := λm : Nat. λn: Nat. iter [Nat] m n succ
plus : Nat -> Nat -> Nat
plus m n = iter @Nat m n succ'

-- 10 

toInt : Nat -> Int
toInt n = iter @Int n 0 (\(k:Int) -> k + 1)

-- Tests (depois apagar)
_ = print "=============TESTS EXERCISE 9 AND 10=============="
 
two' : Nat
two' = succ' (succ' zero)
 
_ = print (toInt (plus zero zero))                  -- expected: 0
_ = print (toInt (plus zero three'))                -- expected: 3
_ = print (toInt (plus three' zero))                -- expected: 3
_ = print (toInt (plus two' three'))                -- expected: 5
_ = print (toInt (plus (plus two' three') three'))  -- expected: 8

-- 11

one : Nat
one = succ' zero

two : Nat
two = succ' one

three : Nat
three = succ' two

-- Tests
_= print "=============TESTS EXERCISE 11=============="
_= print (toInt (plus one two))
_= print (toInt three)

{-
    Resultado obtido de plus one two: 3, igual a three. 
    O plus one two da secção 2 deu o seguinte valor: ΛX. λx1 : (X -> X). λx2 : X. x1 (((two [X]) x1) x2), que é diferente de 3, como provado nesse
exercício (15). Como explicado antes, a avaliação é call-by-value e não reduz debaixo de lambda,
por isso esse redex (((two [X]) x1) x2) nunca é reduzido.
    Aqui, toInt aplica cada numeral para um tipo, base case e step. Os lambdas são aplicados e o redex é reduzido.
    No final, ambos os resultados são 3, contudo os termos obtidos são diferentes, à semelhança do exercício 15 da secção 2.
-}

-- 12

times : Nat -> Nat -> Nat
times m n = iter @Nat m zero (plus n)  

-- Tests
_= print "=============TESTS EXERCISE 12=============="
_= print (toInt (times two three))               -- expected: 6

-- 13

-- Tapl definition of List X = ∀R. (X -> R -> R) -> R -> R
type List a = forall (r:*T) -> r -> (a -> r -> r) -> r

-- 14

-- nil : ∀X. List X
nil : forall (a:*T) -> List a
nil @a @r z s = z

-- cons : ∀X. X -> List X -> List X
cons : forall (a:*T) -> a -> List a -> List a
cons @a x xs = \@(r:*T) (z:r) (s:a -> r -> r) -> s x (xs @r z s)

-- Tests (apagar depois)
_ = print "=============TESTS EXERCISE 14=============="
 
list123 : List Int
list123 = cons @Int 1 (cons @Int 2 (cons @Int 3 (nil @Int)))
 
-- sum of the elements
_ = print (nil @Int @Int 0 (\(x:Int) (acc:Int) -> x + acc))  -- expected: 0
_ = print (list123 @Int 0 (\(x:Int) (acc:Int) -> x + acc))   -- expected: 6
 
-- shows the structure, so the order of the elements can be checked
_ = putStrLn (list123 @String "nil" (\(x:Int) (acc:String) -> show x ++ " : " ++ acc))    -- expected: 1 : 2 : 3 : nil
_ = putStrLn (nil @Int @String "nil" (\(x:Int) (acc:String) -> show x ++ " : " ++ acc))  -- expected: nil

-- 15

null' : forall (a:*T) -> List a -> Bool
null' @a l = l @Bool True (\(x:a) (acc:Bool) -> False)
 
-- Tests (apagar depois)
_ = print "=============TESTS EXERCISE 15=============="
 
_ = print (null' @Int (nil @Int))                    -- expected: True
_ = print (null' @Int (cons @Int 1 (nil @Int)))      -- expected: False
_ = print (null' @Int list123)                       -- expected: False
 
-- an empty list of another element type, and a list whose element is False
_ = print (null' @Bool (nil @Bool))                  -- expected: True
_ = print (null' @Bool (cons @Bool False (nil @Bool))) -- expected: False

-- 16

aNatList : List Nat
aNatList = cons @Nat zero (cons @Nat one (cons @Nat two (cons @Nat (succ' three) (nil @Nat))))

-- Tests (apagar depois)
_ = print "=============TESTS EXERCISE 16=============="
 
_ = print (null' @Nat aNatList)  -- expected: False
 
-- a Nat cannot be printed directly, so each element is converted with toInt
_ = putStrLn (aNatList @String "nil" (\(n:Nat) (acc:String) -> show (toInt n) ++ " : " ++ acc))  -- expected: 0 : 1 : 2 : 4 : nil

-- 17

length : forall (a:*T) -> List a -> Nat
length @a l = l @Nat zero (\(x:a) (acc:Nat) -> succ' acc)


-- Tests
_ = print "=============TESTS EXERCISE 17=============="
 
_ = print (toInt (length @Nat aNatList))                      -- expected: 4

-- (apagar depois)
_ = print (toInt (length @Nat (nil @Nat)))                    -- expected: 0
_ = print (toInt (length @Nat (cons @Nat three (nil @Nat))))  -- expected: 1
_ = print (toInt (length @Int list123))                       -- expected: 3
 
-- 18

sumNats : List Nat -> Nat
sumNats l = l @Nat zero plus

-- Tests
_ = print "=============TESTS EXERCISE 18=============="
 
_ = print (toInt (sumNats aNatList))                     -- expected: 7

-- (apagar depois)
_ = print (toInt (sumNats (nil @Nat)))                   -- expected: 0
_ = print (toInt (sumNats (cons @Nat three (nil @Nat))))   -- expected: 3
_ = print (toInt (sumNats (cons @Nat three aNatList)))     -- expected: 10

-- 19

replicate : forall (a:*T) -> Nat -> a -> List a
replicate @a n v = iter @(List a) n (nil @a) (cons @a v)

four : Nat
four = succ' three

-- Tests
_ = print "=============TESTS EXERCISE 19=============="
 
_ = print (toInt (length @Char (replicate @Char four 'a')))  -- expected: 4

-- (apagar depois)
_ = print (toInt (length @Char (replicate @Char zero 'a')))  -- expected: 0
_ = print (null' @Char (replicate @Char zero 'a'))           -- expected: True
 
-- the length does not check the elements, so they are also shown
_ = putStrLn (replicate @Char four 'a' @String "nil" (\(x:Char) (acc:String) -> show x ++ " : " ++ acc))  -- expected: 'a' : 'a' : 'a' : 'a' : nil
 
-- v can have another type
_ = print (toInt (sumNats (replicate @Nat three two)))      -- expected: 6