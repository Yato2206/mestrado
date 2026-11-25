ghost function power (b: int, n: nat): int
    requires b != 0
    {
        if n == 0 then 1 else b * power(b,n - 1)
    }

method PowerTwoFaster (n: nat) returns (p: nat)
    ensures p == power(2,n)
{
 	var k: nat := n;
	var b: nat := 2;
	p := 1;
	while k > 0
        invariant b > 0
        invariant p * power(b,k) == power(2,n)
    {
        // p * power(b,k) == power(2,n) && k>0
		if (k % 2 != 0){
            //assume p * power(b,k) == power(2,n) && k>0 && k % 2 != 0;
			p := b * p;
			k := k - 1;
            //assert p * power(b,k) == power(2,n);
		}
		else{
            powerProp(b,k);
            //assume p * power(b,k) == power(2,n) && k>0 && k % 2 == 0;
			//assert p * power(b * b,k / 2) == power(2,n);
            k := k / 2;
            //assert p * power(b * b,k) == power(2,n);
			b := b * b;
            //assert p * power(b,k) == power(2,n);
		}
	}
}

lemma powerProp(b: nat, k: nat)
    requires b != 0 && k % 2 == 0
    ensures power(b,k) == power(b * b,k / 2)
{
   if k != 0 {
    powerProp(b, k-2);
   }
}

/*
Descobrir a invariante:

    |    |    |    |    |    |    |
----|----|----|----|----|----|----|
  n |  9 |  9 | 9  | 9  | 9  | 9  |
----|----|----|----|----|----|----|
  k |  9 |  8 |  4 |  2 |  1 |  0 |
----|----|----|----|----|----|----|
  b |  2 |  2 | 2^2| 2^4| 2^8| 2^8|
----|----|----|----|----|----|----|
  p |  1 |  2 |  2 |  2 |  2 | 2^9|
----|----|----|----|----|----|----|

p* b^k = 2^n

*/