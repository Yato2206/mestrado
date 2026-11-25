/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2026
   
   Assignment 2, exercise 4

   ---------------------------------------------------------------------------
   You need to complete the implementation of CharSet class
   and equip it with a MODEL-BASED specification.
   Recall that these specifications are EXCLUSIVELY written in terms 
   of the model (the ghost variables). The method contracts (requires
   and ensures clauses) cannot use ANY fields of the class!

   The specification must be strong enough to allow: 
   1) the verification of the constructor and all the methods of the class
   2) the verification of the Main method 
  --------------------------------------------------------------------------

   Instructor: Antonia Lopes
   Student: Ricardo Pinto 68061
*/

/********************************************************************************* 
* The class CharSet implements a set of characters. The implementation is
* based on a single field of type string (an alias for seq<char>).
**********************************************************************************/

class CharSet {
  /* private */ var s: string

  //the model
  ghost var elems: set<char>

  ghost predicate Valid()
    reads this
    {
      (forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j])
      &&
      forall c :: c in elems <==> c in s
    }

  constructor ()
    ensures Valid()
    ensures elems == {}
  {
    s := []; 
    elems := {};
  }

  method contains(c: char) returns (result : bool)
    requires Valid()
    ensures Valid()
    ensures result <==> c in elems
  {
    var i := 0;
    while i < |s| && s[i] < c 
      invariant 0 <= i <= |s|
      && (forall j :: 0 <= j < i ==> s[j] < c)
    { 
      i := i + 1; 
    }
    result := i < |s| && s[i] == c;
  }

  method isEmpty() returns (result: bool)
    requires Valid()
    ensures Valid()
    ensures elems == old(elems)
    ensures result <==> elems == {}
  {
    result := |s| == 0;
    if |s| > 0 {assert s[0] in elems;}
  }

  method add(c: char)
    modifies this
    requires Valid()
    ensures Valid()
    ensures elems == old(elems) + {c}
  { 
    var i := 0;
    while i < |s| && s[i] < c 
      invariant 0 <= i <= |s|
      && (forall j :: 0 <= j < i ==> s[j] < c)
    { 
      i := i + 1; 
    }
    if (i < |s| && s[i] != c) || (i == |s|) {
        s := s[..i] + [c] + s[i..]; 
         elems := elems + {c};
    }
  }

  method remove(c: char)
    requires Valid()
    modifies this
    ensures Valid()
    ensures elems == old(elems) - {c}
  {
    var i := 0;
    while i < |s| && s[i] < c
      invariant 0 <= i <= |s|
      && (forall j :: 0 <= j < i ==> s[j] < c)
      {
        i := i + 1;
      }
    if (i < |s| && s[i] == c) {
        s := s[..i] + s[i+1..];
        elems := elems - {c};
    }
  }
}

method Main() {
  var cs := new CharSet();
  cs.add('a');
  cs.add('c');
  cs.add('b');

  var result := cs.contains('a');
  assert result;
  result := cs.contains('b');
  assert result;
  result := cs.contains('c');
  assert result;
  result := cs.contains('d');
  assert !result;
  
  cs.remove('b');
  result := cs.contains('b');
  assert !result;
  result := cs.contains('a');
  assert result;
  result := cs.contains('c');
  assert result;
  result := cs.contains('d');
  assert !result;
}