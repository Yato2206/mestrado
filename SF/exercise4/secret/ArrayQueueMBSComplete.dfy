/**
 
 * A bounded queue of integer numbers implemented with a circular array.
 *
 * The code is inspired in
 * https://algs4.cs.princeton.edu/code/edu/princeton/cs/algs4/ResizingArrayQueue.java
 *
 * Exercise: Write a model-based specification for this class.
 * Suggestion: Consider that a queue is modelled by a sequence with its elements.
 */
 class ArrayQueue<T(0)> {
    
    const N := 10   // the initial capacity
     
    //the model
    ghost var elems: seq<T>

    // The actual implementation (also called the concrete state)
    /* private */const q: array<T>    // queue elements
    /* private */var n : nat    // number of elements in the queue
    /* private */var first: nat // index of first element of queue
    /* private */var last: nat  // index of next available slot
 
// The class invariant 
    ghost predicate Valid()
        reads this, this.q
    {
        //representation invariant 
        RepresentationInvariant()
        &&
        // model is given by the abstraction function
        elems == abstractionFunction()
    }

    function abstractionFunction(): seq<T>
    reads this, this.q
    requires RepresentationInvariant()
    {
        if n == 0 then []
        else if first < last then q[first..last]
        else q[first..q.Length] + q[0..last]
    }

    ghost predicate RepresentationInvariant()
        reads this
    {
        (first < q.Length && last < q.Length == N && n <= q.Length) &&
        (first < last ==> n == last - first) &&
        (n > 0 && last <= first ==> n == q.Length - first + last) &&
        (first == last <==> n == 0 || n == q.Length)
    }

    constructor ()
    ensures Valid()
    ensures fresh(this.q)
    ensures elems == []
    {
        q := new T[N];
        n := 0;
        first := 0;
        last := 0;
        new;
        elems := abstractionFunction();
    }

    predicate IsEmpty()
    reads this, this.q
    requires Valid()
    ensures IsEmpty() <==> elems == [] 
    {
        n == 0
    }

    predicate IsFull()
    reads this, this.q
    requires Valid()
    ensures IsFull() <==> |elems| == N
    {
        n == q.Length
    }

    function Peek(): T
    reads this, this.q
    requires Valid()
    requires !IsEmpty()
    ensures Peek() == elems[0]
    {
        q[first]
    }

    method Enqueue(item: T)
    modifies this, this.q
    requires Valid()
    requires !IsFull()
    ensures Valid()
    ensures elems == old(elems) + [item]
    {
        q[last] := item;
        n := n + 1;
        last := last + 1;
        if last == q.Length { last := 0; }
        elems := abstractionFunction();
     }

    method Dequeue() returns (item: T)
    modifies this
    requires Valid()
    requires !IsEmpty()
    ensures Valid()
    ensures elems == old(elems)[1..] && item == old(elems[0])
    {
        item := q[first];
        n := n - 1;
        first := first + 1;
        if first == q.Length { first := 0; }
        elems := abstractionFunction();
     }
}

method Main()
{
    var q := new ArrayQueue<int>();
    assert q.IsEmpty();
    //print q.IsEmpty(); print '\n';
    q.Enqueue(5);
    assert !q.IsEmpty();
    assert !q.IsFull();
    q.Enqueue(25);
    assert !q.IsEmpty();
    var x := q.Peek();
    assert x == 5 && !q.IsEmpty();
    //print x; print '\n';
    assert 5 in q.elems && 25 in q.elems;
    x := q.Dequeue();
    assert x == 5;
    x := q.Dequeue();
    assert x == 25 && q.IsEmpty();
}