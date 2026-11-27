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

-- Tests (depois apagar)
_= print ("=============TESTS EXERCISE 1==============")

left : Sum Int Bool
left = inl @Int @Bool 3

right : Sum Int Bool
right = inr @Int @Bool True

showInt : Int -> String
showInt n = "left " ++ show n

showBool : Bool -> String
showBool b = "right " ++ show b

-- inl: only the left handler runs
_ = putStrLn (cases @Int @Bool @String left showInt showBool)    -- expected: left 3

-- inr: only the right handler runs
_ = putStrLn (cases @Int @Bool @String right showInt showBool)   -- expected: right True

-- the result type c can change (here Int)
_ = print (cases @Int @Bool @Int left (\(n:Int) -> n + 1) (\(b:Bool) -> if b then 1 else 0))    -- expected: 4
_ = print (cases @Int @Bool @Int right (\(n:Int) -> n + 1) (\(b:Bool) -> if b then 1 else 0))   -- expected: 1

-- inl and inr applied directly, without the named values
_ = putStrLn (cases @Int @Bool @String (inl @Int @Bool 7) showInt showBool)       -- expected: left 7
_ = putStrLn (cases @Int @Bool @String (inr @Int @Bool False) showInt showBool)   -- expected: right False

-- 2

showSumVal : forall (a:*T) (b:*T) -> (a -> String) -> (b -> String) -> Sum a b -> String
showSumVal @a @b showA showB s = cases @a @b @String s (\(x:a) -> "inl " ++ showA x) (\(y:b) -> "inr " ++ showB y)

-- Tests (depois apagar)
_= print ("=============TESTS EXERCISE 2==============") 

showInt' : Int -> String
showInt' n = show n

showBool' : Bool -> String
showBool' b = show b

_ = putStrLn (showSumVal @Int @Bool showInt' showBool' left)                   -- expected: inl 3
_ = putStrLn (showSumVal @Int @Bool showInt' showBool' right)                  -- expected: inr True
_ = putStrLn (showSumVal @Int @Bool showInt' showBool' (inl @Int @Bool 7))     -- expected: inl 7
_ = putStrLn (showSumVal @Int @Bool showInt' showBool' (inr @Int @Bool False)) -- expected: inr False

-- 3
five : Sum Int Bool
five = inl @Int @Bool 5

-- Tests
_= print ("=============TESTS EXERCISE 3==============")
_= putStrLn (showSumVal @Int @Bool show show five) -- expected: inl 5

-- 4
fromL : forall (a:*T) (b:*T) -> Sum a b -> a -> a
fromL @a @b s d = cases @a @b @a s (\(x:a) -> x) (\(y:b) -> d)

-- Tests (depois apagar)
_= print ("=============TESTS EXERCISE 4==============")

_ = print (fromL @Int @Bool left 0)                    -- expected: 3 (inl)
_ = print (fromL @Int @Bool right 0)                   -- expected: 0 (default inr)
_ = print (fromL @Int @Bool (inl @Int @Bool 9) 0)      -- expected: 9 (inl)
_ = print (fromL @Int @Bool (inr @Int @Bool True) 20) -- expected: 20 (default inr)

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