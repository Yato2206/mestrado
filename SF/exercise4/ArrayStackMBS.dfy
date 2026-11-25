/**
 * Reliable Software
 * Masters Course on CSE
 * Department of Informatics
 * Faculty of Sciences
 * University of Lisbon
 * October 18, 2019
 * Vasco T. Vasconcelos
 *
 * A model-based specification of a Stack.
 *
 * The model (or the abstract state), a sequence in this case,
 * is kept in a ghost variable.
 * The invariant, function Valid(), also connects the abstract to
 * the concrete state.
 * All contrats are written solely based on the model (variable contents).
 *
 * Illustrates the {:autocontracts} pragma:
 * - no need to explicitely add the invariant (Valid()) in the contracts to
 *   constructors and methods
 * - no need add the reads/modifies clauses in functions, predicates and
 *   methods
 */
class {:autocontracts} Stack<T(0)>   // T can only be instantiated with default-initializable types
{
    // The abstract state which is visible to clients
    ghost var contents: seq<T>

    // The actual implementation (also called the concrete state)
	// This is meant to be hidden from clients
    var elems: array<T>
    var size: nat

    // Invariant, named Valid() as usual
    ghost predicate Valid()
    {
        // The representation invariant
        size <= elems.Length &&
        // The abstraction function: relates abstract and concrete states
        contents == elems[0..size]
    }
    constructor (length : nat)
        ensures contents == []
    {
        size := 0;
        elems := new T[length];
        contents := []; // ghost code
    }
    predicate  IsEmpty()
        ensures IsEmpty() <==> contents == []
    {
        size == 0
    }
    function Top(): T
        requires !IsEmpty()
        ensures Top() == contents[size - 1]
    {
        elems[size - 1]
    }
    method Pop()
        requires !IsEmpty()
        ensures contents == old(contents[0..|contents| - 1])
    {
        size := size - 1;
        contents := elems[0..size]; // ghost code
    }
    method Push(x: T)
        ensures contents == old(contents) + [x]
     {
        if size == elems.Length
        { // resize
            var a := new T[2 * elems.Length + 1];
            forall i | 0 <= i < size { a[i] := elems[i]; }
            elems := a;
        }
        elems[size] := x;
        size := size + 1;
        contents := elems[0..size]; // ghost code
    }
}

method Main()
{
    var s := new Stack<int>(2);
    print s.IsEmpty(); print '\n';
    s.Push(5);
    assert (!s.IsEmpty());
    assert(s.Top() == 5);
    var x := s.Top();
    assert(x == 5);
    s.Push(10);
    s.Push(20);
    print x; print '\n';
}