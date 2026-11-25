/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2025

   Antonia Lopes

   Credits: Cesare Tinelli-CS:5810-University of Iowa and Dafny Tutorial
*/

/*
 * A class Counter that cannot go negative.
 * Exercise: write a property-based specification for this class
 */
class Counter {

   // The actual implementation (also called the concrete state)
	/* private */var inc: nat
    /* private */var dec: nat
	
	// The class invariant 
    ghost predicate Valid()
		reads this
	{
		inc >= dec 
	}

    constructor ()
		ensures Valid()
		ensures Get() == 0
	{
		inc, dec := 0, 0;
	}
	
	// Method implementations. 
	method Inc()
		modifies this
		requires Valid()
		ensures Valid()
		ensures Get() == old(Get())+ 1
	{
		inc := inc + 1;
	}
	method Dec()
		modifies this
		requires Valid()
		requires Get() > 0
		ensures Valid()
		ensures Get() == old(Get()) - 1
	{
		dec := dec + 1;
	}

	method Clear()
		modifies this
		requires Valid()
		ensures Valid()
		ensures Get() == 0
		
	{
    	inc, dec := 0, 0;
	}

	//The observer we use to explain the behavior of the other methods
	//Was made a function since it has no side effects and otherwise could not be used in contracts
	function Get(): nat
		reads this
		requires Valid()
	{
		inc - dec
	}

	method Set(n: nat)
		modifies this
		requires Valid()
		ensures Valid()
		ensures Get() == n
	{
		inc, dec := n, 0;
	}
}

method Main () 
{
    var c := new Counter();  
	
	var val :=  c.Get(); 
    assert (val == 0);     
    c.Set(3);
	c.Dec();c.Dec();
	val :=  c.Get(); 
    assert (val == 1);

	c.Inc(); c.Inc(); c.Inc();
	val :=  c.Get(); 
    assert (val == 4);
   	
	c.Set(3);
	val :=  c.Get(); 
    assert (val == 3);
}