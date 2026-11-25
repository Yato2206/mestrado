method BinarySearch(a: array<int>, key: int) returns (index: int)
  // The array is sorted
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // If the result is non-negative, then a[index] == key
  ensures 0 <= index ==> index < a.Length && a[index] == key
  // If the result is negative, then the key is not in the array
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
{
    var low, high := 0, a.Length;
    while low < high
        invariant 0 <= low <= high <= a.Length
        invariant forall i:: (0 <= i < low || high <=i < a.Length) ==> a[i] != key
    {
        var mid := (low + high) / 2;
        if a[mid] < key { low := mid + 1; }
        else if key < a[mid] { high := mid; }
        else { return mid; }
    }
    return -1;
}

/*
Descobrir a invariante:

low |    |    |midle|    |    |high |
----|----|----|-----|----|----|----|
  n |  .----> |  0  |   < - - | -. |
----|----|----|-----|----|----|----|

c * [ something [] * []]

*/