-- 1

-- ∀X. (T -> X) -> (U -> X) -> X
type Sum a b = forall (c:*T) -> (a -> c) -> (b -> c) -> c

-- inl := lambda X1 . (lambda X2 . (lambda x : X1 . (lambda X . (lambda x1 : (X1 -> X) . (lambda x2 : (X2 -> X) . (x1 x))))))
inl : forall (a:*T) (b:*T) -> a -> Sum a b
inl @a @b x = \@(c:*T) (f:a -> c) (g:b -> c) -> f x

-- inr := lambda X1 . (lambda X2 . (lambda x : X2 . (lambda X . (lambda x1 : (X1 -> X) . (lambda x2 : (X2 -> X) . (x2 x))))))
inr : forall (a:*T) (b:*T) -> b -> Sum a b
inr @a @b y = \@(c:*T) (f:a -> c) (g:b -> c) -> g y

--cases :=  lambda X1 . (lambda X2 . (lambda X3 . (lambda x : (X1 sum X2) . (lambda x1 : (X1 -> X3) . (lambda x2 : (X2 -> X3) . 
--    (((x {X3}) x1) x2))))))
cases : forall (a:*T) (b:*T) (c:*T) -> Sum a b -> (a -> c) -> (b -> c) -> c
cases @a @b @c s f g = s @c f g

-- 2

showSumVal : forall (a:*T) (b:*T) -> (a -> String) -> (b -> String) -> Sum a b -> String
showSumVal @a @b showA showB s = cases @a @b @String s (\(x:a) -> "inl " ++ showA x) (\(y:b) -> "inr " ++ showB y)

-- 3
five : Sum Int Bool
five = inl @Int @Bool 5

-- Tests
_= print ("=============TESTS EXERCISE 3==============")
_= putStrLn (showSumVal @Int @Bool show show five) -- expected: inl 5

-- 4
fromL : forall (a:*T) (b:*T) -> Sum a b -> a -> a
fromL @a @b s d = cases @a @b @a s (\(x:a) -> x) (\(y:b) -> d)

-- 5
v5: Sum Int Bool
v5 = inl 435

-- Tests
_= print ("=============TESTS EXERCISE 5==============")
_= print (fromL v5 0) -- expected: 435 (inl)

-- 6
v6: Sum Int Bool
v6 = inr True

-- Tests
_= print ("=============TESTS EXERCISE 6==============")
_= print (fromL v6 0) -- expected: 0 (default inr)