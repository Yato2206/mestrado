-- 7
type Nat = forall (c:*T) -> c -> (c -> c) -> c

-- zero := λX. λs: X -> X. λz: X . z
zero : Nat
zero @c z s = z

-- succ := λn:CNat. λX. λs: X -> X. λz:X . s (n [X] s z)
succ' : Nat -> Nat
succ' n = \@(c:*T) (z:c) (s:c -> c) -> s (n @c z s)

-- 8

-- iter = Λc. λn: Nat. λz: c. λs: c -> c. n [c] s z
iter : forall (c:*T) -> Nat -> c -> (c -> c) -> c
iter @c n z s = n @c z s
 
 -- 9

-- plus := λm : Nat. λn: Nat. iter [Nat] m n succ
plus : Nat -> Nat -> Nat
plus m n = iter @Nat m n succ'

-- 10 

toInt : Nat -> Int
toInt n = iter @Int n 0 (\(k:Int) -> k + 1)

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
exercício (15). Como explicado antes, q avaliação é call-by-value e não reduz debaixo de lambda,
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

-- 15

null' : forall (a:*T) -> List a -> Bool
null' @a l = l @Bool True (\(x:a) (acc:Bool) -> False)
 
-- 16

aNatList : List Nat
aNatList = cons @Nat zero (cons @Nat one (cons @Nat two (cons @Nat (succ' three) (nil @Nat))))

-- 17

length : forall (a:*T) -> List a -> Nat
length @a l = l @Nat zero (\(x:a) (acc:Nat) -> succ' acc)

-- Tests
_ = print "=============TESTS EXERCISE 17=============="
_ = print (toInt (length @Nat aNatList))                      -- expected: 4

-- 18

sumNats : List Nat -> Nat
sumNats l = l @Nat zero plus

-- Tests
_ = print "=============TESTS EXERCISE 18=============="
_ = print (toInt (sumNats aNatList))                     -- expected: 7

-- 19

replicate : forall (a:*T) -> Nat -> a -> List a
replicate @a n v = iter @(List a) n (nil @a) (cons @a v)

four : Nat
four = succ' three

-- Tests
_ = print "=============TESTS EXERCISE 19=============="
_ = print (toInt (length @Char (replicate @Char four 'a')))  -- expected: 4
