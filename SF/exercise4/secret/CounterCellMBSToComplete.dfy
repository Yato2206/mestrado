/*

   Credits: Paper about Dafny by Rustan Leino
*/

/*
 * A class Counter equipped with a model-based specification.
 * Exercise: write a model-based specification for this class
 * and use dynamic frames to specify the methods of the class
 * without exposing the internal representation.
 */

class Cell{
    var data: nat
}

class Counter {
	//The model
	ghost var val: int

   // The actual implementation (also called the concrete state)
	/* private */var inc: Cell
    /* private */var dec: Cell

	
	// The class invariant 
    ghost predicate Valid()
	{
		true //toComplete 
		//add representation invariant
	}

    constructor ()
	{
		inc := new Cell;
		dec := new Cell;
         new;
		inc.data, dec.data := 0, 0;
		//add ghost code
	}
	
	// Method implementations. 
	method Inc()
	{
		inc.data := inc.data + 1;
		//add ghost code
	}
	method Dec()
	{
		dec.data := dec.data + 1;
		//add ghost code
	}
	method Clear()
	{
    	inc.data, dec.data := 0, 0;
		//add ghost code
	}
	function Get(): int
	{
		inc.data - dec.data
	}

	method Set(n: int)
	{
 		//toComplete
		//add ghost code
	}

}

method Main () 
{
    var c := new Counter();  
	
	var val :=  c.Get(); 
    assert (val == 0);     
    
	c.Dec(); c.Dec();
	val :=  c.Get(); 
    assert (val == -2);

	c.Inc(); c.Inc(); c.Inc();
	val :=  c.Get(); 
    assert (val == 1);
   	
	c.Set(3);
	val :=  c.Get(); 
    assert (val == 3);
}