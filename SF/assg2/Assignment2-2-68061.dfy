/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2026
   
   All Nines, assignment 2, exercise 2

   Instructor: Antonia Lopes
   Student: Ricardo Pinto 68061
*/

// função recursiva para calcular 10^n
ghost function powerTen(n: nat) : nat 
{
	if n == 0 then 1
    else 10 * powerTen(n - 1)
}

method AllNines(n: nat) returns (num: nat)
requires n > 0 
ensures num == powerTen(n) - 1
{
	num := 9;
    var i := 1;
	while (i < n) 
        invariant num == powerTen(i) - 1
        invariant i <= n
    {
		num := num * 10 + 9;
		i := i + 1;
	}
}

method main() 
{
    // Test the AllNines method with different values of n
    var n := 1;
    var num := AllNines(n); // num = 9
    assert num == powerTen(n) - 1;  // 9 == 10^1 - 1 

    var n2 := 9;
    var num2 := AllNines(n2); // num2 = 999999999
    assert num2 == powerTen(n2) - 1;  // 999999999 == 10^9 - 1
}                                                                                                                                                                                                                                                                                                                                                                                