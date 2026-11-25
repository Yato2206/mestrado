method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index <= a.Length
  ensures index < a.Length ==> a[index] == key
  ensures index == a.Length ==> forall k :: 0 <= k < index ==> a[k] != key
{
    index := 0;
    while index < a.Length && a[index] != key 
    //achar a invariante
    invariant 0 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> a[i] != key
    {
        index := index + 1;
    }
}
