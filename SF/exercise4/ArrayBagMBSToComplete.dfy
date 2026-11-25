/**
 * Reliable Software
 * Masters Course on CSE
 * Department of Informatics
 * Faculty of Sciences
 * University of Lisbon
 * 
 * Vasco T. Vasconcelos
 * Antonia Lopes
 *
 * An unbounded bag of chars implemented with a growing array.
 *
 * Exercise: Write a model-based specification for this class; do not use auto-contracts.
 *
 */
 class Bag
{
    //the model
    
    
    // The actual implementation (also called the concrete state)
    /* private */var a : array<char>
    /* private */var n : nat

	// The class invariant 
    ghost predicate Valid ()
        reads this, a
    {
        //representation invariant
        // model given by the abstraction function
        true
    }

    constructor ()
    {
        n, a := 0, new char[10];
        new;
        // ghost code
        
    }

    method Add (elem : char)
    {
        if n == a.Length
        { // resize
            var b := new char[2 * a.Length + 1];
            var i := 0;
            while i < n
            {
                b[i] := a[i];
                i := i + 1;
            }
            a := b;
        }
        a[n] := elem;
        n := n + 1;
        // ghost code

    }
   
    method ExtractMin () returns (m: char)
    {
        var mindex := 0;
        var i := 1;
        while i < n
            invariant mindex < n
            invariant i <= n
            invariant isMin(a[mindex], multiset(a[..i]))
        {
            if a[i] < a[mindex] { mindex := i; }
            i := i + 1;
        }
        m := a[mindex];
        n := n - 1;
        a[mindex] := a[n];
        // ghost code

        // call lemma about the min
    }
    method Size () returns (s: nat)
    {
        return n;
    }

}

predicate isMin (x: char, s: multiset<char>)
    ensures isMin(x,s) ==> x in s && s != multiset{} 
 {
     x in s && forall y :: (y in s ==> x <= y)
 }

 function minC(x:char, y: char):char{
    if x <= y then x else y
 } 

 ghost function min (s: multiset<char>): char
     requires s != multiset{}
     ensures min(s) in s
  {
     var ch :| ch in s;
     if |s| == 1 then ch 
     else
         var s2 := s - multiset{ch};
         if min(s2) < ch then min(s2) else ch
 }


 lemma minIsMin (x: char, s: multiset<char>)
    requires s != multiset{}
    ensures  isMin(x,s) ==> min(s) == x
    decreases |s|
{
    var ch :| ch in s;
    if s == multiset{ch} {
        assert min(s) == ch;
        assert isMin(ch, s);
    }
    else {
        minIsMin(x, s-multiset{ch});
    }
}


method Test ()
{
    var b := new Bag();
    var n;
    n := b.Size(); assert n == 0;
    b.Add('b');
    n := b.Size(); assert n == 1;
    b.Add('a'); b.Add('a');
    //assert b.contents == multiset{'a','a','b'};
    n := b.Size(); assert n == 3;
    var x;
    x := b.ExtractMin(); 
    assert x == 'a';
    n := b.Size(); 
    assert n == 2;
    x := b.ExtractMin(); 
    assert x == 'a';
    n := b.Size(); 
    assert n == 1;
    x := b.ExtractMin(); 
    assert x == 'b';
    n := b.Size(); 
    assert n == 0;
}


 
method Main ()
{
    var b := new Bag();
    var n;
    n := b.Size(); print n; print '\n';
    b.Add('b');
    n := b.Size(); print n; print '\n';
    b.Add('a'); b.Add('a');
    n := b.Size(); print n; print '\n';
    var c;
    c := multiset(b.a[..b.n]); print c; print '\n';
    var x;
    x := b.ExtractMin(); print x; print '\n';
    n := b.Size(); print n; print '\n';
    c := multiset(b.a[..b.n]); print c; print '\n';
    x := b.ExtractMin(); print x; print '\n';
    n := b.Size(); print n; print '\n';
    c := multiset(b.a[..b.n]); print c; print '\n';
    x := b.ExtractMin(); print x; print '\n';
    n := b.Size(); print n; print '\n';
}