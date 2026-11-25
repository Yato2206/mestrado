/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2022

   Antonia Lopes

   Credits: Cesare Tinelli-CS:5810-University of Iowa
   and Dafny Tutorial
*/

/*
 * A class Counter.
 * Exercise: write a property-based specification for this class
 */
class Counter {

   // The actual implementation (also called the concrete state)
	/* private */var inc: nat
    /* private */var dec: nat
	/*
		com int em vez de nat:
			preciso de adicionar algo read this a Valid()
			necessário definir a invariante
		no constructor é preciso adicionar ensures Valid()
		nos métodos que não sejam observer adicionar ensures Valid() e requires Valid()
	*/


	// The class invariant 
    predicate Valid()
	//read this
	{
		true //toComplete
		// inc >= 0 && dec >= 0
	}

    constructor ()
	//ensures Valid()
	ensures Get() == 0 
	{
		inc, dec := 0, 0;
	}
	
	// Method implementations. 
	method Inc()
	modifies this
	//ensures Valid()
	//requires Valid()
	ensures Get() == old(Get()) + 1 
	{
		inc := inc + 1;
	}
	method Dec()
	//ensures Valid()
	//requires Valid()
	modifies this
	ensures Get() == old(Get() - 1)
	{
		dec := dec + 1;
	}

	method Clear()
	//ensures Valid()
	//requires Valid()
	ensures Get() == 0
	modifies this
	{
    	inc, dec := 0, 0;
	}
	function Get(): (int)
	reads this
	{
		inc - dec
	}

	method Set(n: int)
	//ensures Valid()
	//requires Valid()
	ensures Get() == n
	modifies this
	{
		if (n > 0) {
			inc := n;
			dec := 0;
		}
		else {
			inc := 0;
			dec := -n;
		}
	}
}

method Main () 
{
    var c := new Counter();  
	
	var val :=  c.Get(); 
    assert (val == 0);     
    
	c.Dec();c.Dec();
	val :=  c.Get(); 
    assert (val == -2);

	c.Inc(); c.Inc(); c.Inc();
	val :=  c.Get(); 
    assert (val == 1);
   	
	c.Set(3);
	val :=  c.Get(); 
    assert (val == 3);
}