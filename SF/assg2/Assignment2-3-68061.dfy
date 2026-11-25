/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2026
   
   Counting Sort, assignment 2, exercise 3

   Instructor: Antonia Lopes
   Student: Ricardo Pinto 68061

   Include here any other information you consider relevant for the assignment

*/

/*----------------------------------------------------------------
  Frequencies: Specification helpers, implementation and lemmas
------------------------------------------------------------------*/

//SPECIFICATION HELPERS

ghost function NumberOfOccurrences<T>(a: seq<T>, v: T): nat
{
  if |a| == 0 then 0
  else 
    (if a[0] == v then 1 else 0) + NumberOfOccurrences(a[1..], v)
}

//LEMMAS

/*
  Occurrences are additive over concatenation: occ(s + t, v) == occ(s, v) + occ(t, v).
 The recursive definition only peels off the head of a sequence, so Dafny cannot see this on its own.
*/
lemma NumberOfOccurrencesConcat<T>(s: seq<T>, t: seq<T>, v: T)
  ensures NumberOfOccurrences(s + t, v) == NumberOfOccurrences(s, v) + NumberOfOccurrences(t, v)
{
  if |s| > 0 {
    assert (s + t)[0] == s[0] && (s + t)[1..] == s[1..] + t;
    NumberOfOccurrencesConcat(s[1..], t, v);
  } else {
    assert s + t == t;
  }
}

/* 
  Adding one element x at the end of s increases the count of v by 1 if x == v, else by 0.
Both loops process the input one element at a time, a[..i] becoming a[..i+1] == a[..i] + [a[i]]. 
*/
lemma NumberOfOccurrencesAppend<T>(s: seq<T>, v: T, x: T)
  ensures NumberOfOccurrences(s + [x], v) == NumberOfOccurrences(s, v) + (if x == v then 1 else 0)
{
  NumberOfOccurrencesConcat(s, [x], v);
}

//IMPLEMENTATION

method Frequencies(a: array<nat>, k: nat) returns (result: array<nat>)
  requires forall i :: 0 <= i < a.Length ==> a[i] < k
  ensures result.Length == k
  ensures forall v: nat :: 0 <= v < k ==> result[v] == NumberOfOccurrences(a[..], v)
  ensures fresh(result)
{
  result := new nat[k] (_ => 0);
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == k
    invariant forall v: nat :: v < k ==> result[v] == NumberOfOccurrences(a[..i], v)
  {
    assert a[..i + 1] == a[..i] + [a[i]];
    forall v: nat | v < k
      ensures NumberOfOccurrences(a[..i + 1], v) == NumberOfOccurrences(a[..i], v) + (if a[i] == v then 1 else 0)
    { NumberOfOccurrencesAppend(a[..i], v, a[i]); }
    result[a[i]] := result[a[i]] + 1;
    i := i + 1;
  }
  assert a[..i] == a[..];
}

/*----------------------------------------------------------------
  CountingSort: Specification helpers, implementation and lemmas
------------------------------------------------------------------*/

//SPECIFICATION HELPERS

/*
  NumberOfLessThan(s, v) is the number of elements of `s` that are strictly less than v.
In counting sort, the position where the block of v's must start in the sorted output is
exactly the number of elements smaller than v. So NumberOfLessThan(a, v) is the first
slot of the "bucket" of v, and the prefix sums computed by the first loop of
CountingSort are values of this function.
*/
ghost function NumberOfLessThan(s: seq<nat>, v: nat): nat
{
  if |s| == 0 then 0
  else 
    (if s[0] < v then 1 else 0) + NumberOfLessThan(s[1..], v)
}

ghost predicate isSorted(s: seq<nat>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}


/*
  Bucket of v = the range of positions [NumberOfLessThan(a, v), NumberOfLessThan(a, v + 1))
of the sorted output. BucketsFilled(a, r, k) says that every position of r inside the
bucket of some v < k holds exactly v.
It is the bridge between the loop and the final result. The second loop of CountingSort
maintains it for the slots written so far.
 */
ghost predicate BucketsFilled(a: seq<nat>, r: seq<nat>, k: nat)
{
  forall v: nat, p: nat ::
    v < k && NumberOfLessThan(a, v) <= p < NumberOfLessThan(a, v + 1) && p < |r| ==> r[p] == v
}

//LEMMAS

/*
  No element is smaller than 0 (nat), so NumberOfLessThan(s, 0) == 0.
It gives the initial value of the loop invariant of the prefix-sum loop in CountingSort (total == NumberOfLessThan(a[..], 0) when j == 0).
*/
lemma NumberOfLessThanZero(s: seq<nat>)
  ensures NumberOfLessThan(s, 0) == 0
{}

/*
  #(<v+1) == #(<v) + occ(v): the elements below v+1 are those below v plus those equal to v.
Central to the bucket structure. The bucket of v ends where the bucket of v+1 begins, and
its size is occ(v). 
*/
lemma NumberOfLessThanSuccessor(s: seq<nat>, v: nat)
  ensures NumberOfLessThan(s, v + 1) == NumberOfLessThan(s, v) + NumberOfOccurrences(s, v)
{
  if |s| > 0 { NumberOfLessThanSuccessor(s[1..], v); }
}

/*
  NumberOfLessThan is monotone in its second argument: v <= w ==> #(<v) <= #(<w).
It orders the buckets: if v < w, the bucket of v lies entirely before the bucket of w.
*/
lemma NumberOfLessThanMonotone(s: seq<nat>, v: nat, w: nat)
  requires v <= w
  ensures NumberOfLessThan(s, v) <= NumberOfLessThan(s, w)
{}

/*
  If every element of s is < k, then NumberOfLessThan(s, k) == |s|.
This is where the precondition "all values are < k" is used.
*/
lemma NumberOfLessThanAll(s: seq<nat>, k: nat)
  requires forall i :: 0 <= i < |s| ==> s[i] < k
  ensures NumberOfLessThan(s, k) == |s|
{}

/*
  A prefix has no more occurrences of v than the whole sequence: occ(s[..i], v) <= occ(s, v).
It keeps each counter inside its own bucket. With i + 1 in place of i it also gives
occ(a[..i+1], x) <= occ(a, x), hence count[x] < #(<x+1): the slot about to be written
belongs to the bucket of x. Without it, nothing prevents the buckets from overflowing.
*/
lemma NumberOfOccurrencesPrefix<T>(s: seq<T>, i: nat, v: T)
  requires i <= |s|
  ensures NumberOfOccurrences(s[..i], v) <= NumberOfOccurrences(s, v)
{
  assert s == s[..i] + s[i..];
  NumberOfOccurrencesConcat(s[..i], s[i..], v);
}

/*
  If every element of s equals v, then occ(s, v) == |s|.
Used by NumberOfOccurrencesOfBlock: inside the bucket of v every slot holds v, so the
bucket contributes exactly its length to the count of v.
*/
lemma NumberOfOccurrencesAllEqual<T>(s: seq<T>, v: T)
  requires forall i :: 0 <= i < |s| ==> s[i] == v
  ensures NumberOfOccurrences(s, v) == |s|
  decreases |s|
{
  if |s| > 0 {
    assert forall i :: 0 <= i < |s[1..]| ==> s[1..][i] == v by {
      forall i | 0 <= i < |s[1..]| ensures s[1..][i] == v { assert s[1..][i] == s[i + 1]; }
    }
    NumberOfOccurrencesAllEqual(s[1..], v);
  }
}

/*
  If no element of s equals v, then occ(s, v) == 0.
Used for the parts of the output outside the bucket of v (they contain no v) and for
values v >= k, which appear neither in the input nor in the output.
*/
lemma NumberOfOccurrencesNone<T>(s: seq<T>, v: T)
  requires forall i :: 0 <= i < |s| ==> s[i] != v
  ensures NumberOfOccurrences(s, v) == 0
  decreases |s|
{
  if |s| > 0 {
    assert forall i :: 0 <= i < |s[1..]| ==> s[1..][i] != v by {
      forall i | 0 <= i < |s[1..]| ensures s[1..][i] != v { assert s[1..][i] == s[i + 1]; }
    }
    NumberOfOccurrencesNone(s[1..], v);
  }
}

/*
  Find the bucket that contains position p in the sequence s.
It shows that the buckets cover every position of the output, so every slot of the
result is accounted for. Used by PositionBucket.
*/
lemma FindBucket(s: seq<nat>, k: nat, p: nat)
  requires p < NumberOfLessThan(s, k)
  ensures exists v: nat :: v < k && NumberOfLessThan(s, v) <= p < NumberOfLessThan(s, v + 1)
{
   if k > 0 && p < NumberOfLessThan(s, k - 1) { FindBucket(s, k - 1, p); }
}

/*
   If a sequence has no v before `lower`, only v on [lower, higher], and no v from `higher`
on, then it contains exactly higher - lower occurrences of v.
*/
lemma NumberOfOccurrencesOfBlock<T>(r: seq<T>, lower: nat, higher: nat, v: T)
  requires lower <= higher <= |r|
  requires forall i :: 0 <= i < lower ==> r[i] != v
  requires forall i :: lower <= i < higher ==> r[i] == v
  requires forall i :: higher <= i < |r| ==> r[i] != v
  ensures NumberOfOccurrences(r, v) == higher - lower
{
  assert r == r[..lower] + (r[lower..higher] + r[higher..]);
  NumberOfOccurrencesNone(r[..lower], v);
  NumberOfOccurrencesAllEqual(r[lower..higher], v);
  NumberOfOccurrencesNone(r[higher..], v);
  NumberOfOccurrencesConcat(r[..lower], r[lower..higher] + r[higher..], v);
  NumberOfOccurrencesConcat(r[lower..higher], r[higher..], v);
}

/*
  If all buckets are filled, every position p of r lies in the bucket of some w < k and
r[p] == w, i.e. we know exactly which value is at p.
Combines FindBucket (p has a bucket) with BucketsFilled (that bucket holds its value).
It is the basic fact used to compare two positions for sortedness, and to show that positions
outside the bucket of v do not hold v.
*/
lemma PositionBucket(a: seq<nat>, r: seq<nat>, k: nat, p: nat)
  requires NumberOfLessThan(a, k) == |a| == |r| && BucketsFilled(a, r, k) && p < |r|
  ensures exists w: nat :: w < k && NumberOfLessThan(a, w) <= p < NumberOfLessThan(a, w + 1) && r[p] == w
{
  FindBucket(a, k, p);
}

/*
    Key lemma. If all buckets of r are filled (BucketsFilled) and every value of a is < k, then
  (1) r is sorted: if i < j, with r[i] == v and r[j] == w, then v <= w, because otherwise
j would lie in a bucket that comes before the bucket of v, contradicting i < j;
  (2) r has the same occurrences of every value as a (it is a permutation of a): for
v < k the bucket of v holds exactly occ(a, v) copies of v and no other position holds
v, and for v >= k both sequences have none.
It turns the loop's bucket-by-bucket invariant into the two postconditions that
CountingSort promises, keeping the final proof out of the method body.
*/
lemma BucketsImplySortedPermutation(a: seq<nat>, r: seq<nat>, k: nat)
  requires forall i :: 0 <= i < |a| ==> a[i] < k
  requires |r| == |a| && BucketsFilled(a, r, k)
  ensures isSorted(r)
  ensures forall v: nat :: NumberOfOccurrences(r, v) == NumberOfOccurrences(a, v)
{
  NumberOfLessThanAll(a, k);
  forall p: nat | p < |r| { PositionBucket(a, r, k, p); }

  // sorted: if r[i] = v > w = r[j] with i < j, then j would lie before the bucket of v
  forall i, j | 0 <= i < j < |r| ensures r[i] <= r[j] {
    var v: nat :| v < k && NumberOfLessThan(a, v) <= i < NumberOfLessThan(a, v + 1) && r[i] == v;
    var w: nat :| w < k && NumberOfLessThan(a, w) <= j < NumberOfLessThan(a, w + 1) && r[j] == w;
    if w < v { NumberOfLessThanMonotone(a, w + 1, v); }
  }

  // permutation
  forall v: nat ensures NumberOfOccurrences(r, v) == NumberOfOccurrences(a, v) {
    if v >= k {
      NumberOfOccurrencesNone(a, v);
      NumberOfOccurrencesNone(r, v);
    } else {
      var lo, hi := NumberOfLessThan(a, v), NumberOfLessThan(a, v + 1);
      NumberOfLessThanSuccessor(a, v);
      NumberOfLessThanMonotone(a, v + 1, k);
      NumberOfOccurrencesOfBlock(r, lo, hi, v);
    }
  }
}

//IMPLEMENTATION

method CountingSort(a: array<nat>, k: nat) returns (result: array<nat>)
  requires forall i:: 0 <= i < a.Length ==> a[i] < k
  ensures result.Length == a.Length
  ensures isSorted(result[..])
  ensures forall v: nat :: NumberOfOccurrences(result[..], v) == NumberOfOccurrences(a[..], v)
{
  var count := Frequencies(a, k);

  var total := 0;
  var j := 0;

  NumberOfLessThanZero(a[..]);

  while j < k
    invariant 0 <= j <= k && count.Length == k
    invariant total == NumberOfLessThan(a[..], j)
    invariant forall v: nat :: v < j ==> count[v] == NumberOfLessThan(a[..], v)
    invariant forall v: nat :: j <= v < k ==> count[v] == NumberOfOccurrences(a[..], v)
  {
    NumberOfLessThanSuccessor(a[..], j);
    count[j], total := total, total + count[j];
    j := j + 1;
  }

  result := new nat[a.Length] (_ => 0);
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length && result.Length == a.Length && count.Length == k
    // count[v] is the next free slot of the bucket of v ...
    invariant forall v: nat :: v < k ==>
      count[v] == NumberOfLessThan(a[..], v) + NumberOfOccurrences(a[..i], v)
    // ... and the slots already filled in the bucket of v hold v
    invariant forall v: nat, p: nat ::
      v < k && NumberOfLessThan(a[..], v) <= p < count[v] && p < result.Length ==> result[p] == v
  {
    ghost var x := a[i];
    assert a[..i + 1] == a[..i] + [x];
    NumberOfOccurrencesAppend(a[..i], x, x);
    NumberOfOccurrencesPrefix(a[..], i + 1, x);
    NumberOfLessThanSuccessor(a[..], x);
    // the buckets of different values are disjoint, so writing in the bucket of x keeps the others
    forall v: nat | v < k && v != x
      ensures count[x] < NumberOfLessThan(a[..], v)
           || NumberOfLessThan(a[..], v) + NumberOfOccurrences(a[..i], v) <= count[x]
    {
      NumberOfLessThanSuccessor(a[..], v);
      NumberOfOccurrencesPrefix(a[..], i, v);
      if v < x { NumberOfLessThanMonotone(a[..], v + 1, x); }
      else     { NumberOfLessThanMonotone(a[..], x + 1, v); }
    }
    // count[x] < a.Length
    NumberOfLessThanAll(a[..], k);
    NumberOfLessThanMonotone(a[..], x + 1, k);

    ghost var oldCount, oldResult := count[..], result[..];
    forall v: nat | v < k
      ensures NumberOfOccurrences(a[..i + 1], v) == NumberOfOccurrences(a[..i], v) + (if x == v then 1 else 0)
    { NumberOfOccurrencesAppend(a[..i], v, x); }

    result[count[a[i]]] := a[i];
    count[a[i]] := count[a[i]] + 1;

    forall v: nat, p: nat | v < k && NumberOfLessThan(a[..], v) <= p < count[v] && p < result.Length
      ensures result[p] == v
    {
      if v == x { if p < oldCount[x] { assert result[p] == oldResult[p]; } else { assert p == oldCount[x]; } }
      else { assert count[v] == oldCount[v] && p != oldCount[x]; assert result[p] == oldResult[p]; }
    }
    i := i + 1;
  }

  assert a[..i] == a[..];
  forall v: nat | v < k
    ensures NumberOfLessThan(a[..], v + 1) == NumberOfLessThan(a[..], v) + NumberOfOccurrences(a[..], v)
  { NumberOfLessThanSuccessor(a[..], v); }
  BucketsImplySortedPermutation(a[..], result[..], k);
}

// Tests of the isSorted predicate on concrete sequences (kept in a lemma so Main's proof stays small)
lemma IsSortedTests()
{
  // Positive tests: sorted sequences (empty, singleton, repeated values, strictly increasing)
  assert isSorted([]);
  assert isSorted([7]);
  assert isSorted([2, 2, 2]);
  assert isSorted([0, 1, 2, 3, 3, 4, 4, 5, 31]);

  // Negative tests: for each unsorted sequence, a witness pair of positions i < j with s[i] > s[j]
  assert !isSorted([2, 1]) by {
    assert 0 < 1 < |[2, 1]| && [2, 1][0] > [2, 1][1];
  }
  assert !isSorted([1, 2, 3, 4, 5, 4, 3, 31, 0]) by {
    var s := [1, 2, 3, 4, 5, 4, 3, 31, 0];
    assert 0 < 8 < |s| && s[0] > s[8];
  }
  assert !isSorted([0, 1, 3, 2, 4]) by {
    var s := [0, 1, 3, 2, 4];
    assert 2 < 3 < |s| && s[2] > s[3];
  }
}


method Main()
{
  // Test the NumberOfOccurrences function
  var a1 := [1, 2, 3, 4, 5, 4, 3, 31, 0];
  var nOccurrences := NumberOfOccurrences(a1, 0);
  assert nOccurrences == 1;
  nOccurrences := NumberOfOccurrences(a1, 1);
  assert nOccurrences == 1;
  nOccurrences := NumberOfOccurrences(a1, 2);
  assert nOccurrences == 1;
  nOccurrences := NumberOfOccurrences(a1, 3);
  assert nOccurrences == 2;
  nOccurrences := NumberOfOccurrences(a1, 4);
  assert nOccurrences == 2;
  nOccurrences := NumberOfOccurrences(a1, 5);
  assert nOccurrences == 1;
  nOccurrences := NumberOfOccurrences(a1, 31);
  assert nOccurrences == 1;
  nOccurrences := NumberOfOccurrences(a1, 61);
  assert nOccurrences == 0;

  // Test the Frequencies method
  var a2 := new nat[9];
  a2[0] := 1;
  a2[1] := 2;
  a2[2] := 3;
  a2[3] := 4;
  a2[4] := 5;
  a2[5] := 4;
  a2[6] := 3;
  a2[7] := 31;
  a2[8] := 0;
  assert a2[..] == [1, 2, 3, 4, 5, 4, 3, 31, 0];

  var freqs := Frequencies(a2, 64);

  // Check the length
  assert freqs.Length == 64;

  // Check the frequencies
  assert freqs[0] == 1;
  assert freqs[1] == 1;
  assert freqs[2] == 1;
  assert freqs[3] == 2; 
  assert freqs[4] == 2; 
  assert freqs[5] == 1;
  assert freqs[31] == 1; 
  // Check values that do not appear
  assert freqs[61] == 0;

  // Test the NumberOfLessThan function
  var nLessThan := NumberOfLessThan(a1, 0);
  assert nLessThan == 0;
  nLessThan := NumberOfLessThan(a1, 1);
  assert nLessThan == 1;
  nLessThan := NumberOfLessThan(a1, 2);
  assert nLessThan == 2;
  nLessThan := NumberOfLessThan(a1, 61);
  assert nLessThan == 9;

  // Test the CountingSort method
  var sorted := CountingSort(a2, 64);
  // Check length
  expect sorted.Length == 9, "Incorrect result length";
  // Check the complete sorted output
  expect sorted[0] == 0;
  expect sorted[1] == 1;
  expect sorted[2] == 2;
  expect sorted[3] == 3;
  expect sorted[4] == 3;
  expect sorted[5] == 4;
  expect sorted[6] == 4;
  expect sorted[7] == 5;
  expect sorted[8] == 31;

   // Test the isSorted predicate
  IsSortedTests();

  // The output of CountingSort is sorted and has the same occurrences as the input
  assert isSorted(sorted[..]);
  assert forall v: nat :: NumberOfOccurrences(sorted[..], v) == NumberOfOccurrences(a2[..], v);
}

  
