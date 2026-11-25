/**
 *
 * Exercise: Write a model-based specification for this class.
 * Suggestion: Consider that a queue is modelled by a sequence with its elements.
 */
 class ArrayQueue<T(0)> {
    
    const N := 10   // the initial capacity
     
    //the model
    //ghost var  TODO

    // The actual implementation (also called the concrete state)
    /* private */var q: array<T>;    // queue elements
    /* private */var n : nat;    // number of elements in the queue
    /* private */var first: nat; // index of first element of queue
    /* private */var last: nat;  // index of next available slot
 
// The class invariant 
    ghost predicate Valid()
        reads this, this.q
    {
        //representation invariant 
        RepresentationInvariant()
        &&
        // model is given by the abstraction function
        /// TODO == abstractionFunction()
    }

    function abstractionFunction(): TODO
    {
        //TODO
    }

    ghost predicate RepresentationInvariant()
        reads this
    {
        //TODO
    }

    constructor ()
    {
        q := new T[N];
        n := 0;
        first := 0;
        last := 0;
    }
    predicate IsEmpty()
    {
        n == 0
    }
    predicate IsFull()
    {
        n == q.Length
    }
    method Peek() returns (item: T)
    {
        item := q[first];
    }
    method Enqueue(item: T)
    {
        q[last] := item;
        n := n + 1;
        last := last + 1;
        if last == q.Length { last := 0; }
     }
    method Dequeue() returns (item: T)
    {
        item := q[first];
        n := n - 1;
        first := first + 1;
        if first == q.Length { first := 0; }
     }
}

method Main()
{
    var q := new ArrayQueue<int>();
    print q.IsEmpty(); print '\n';
    q.Enqueue(5);
    var x := q.Peek();
    print x; print '\n';
}