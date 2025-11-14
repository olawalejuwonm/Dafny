method binSearch(a:array<int>, k:int) returns (index: int)
    requires  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] 
    ensures   exists i: int :: (0 <= i < a.Length && a[i] == k)  ==> index == i
    ensures !(exists i: int :: (0 <= i < a.Length && a[i] == k)) ==> index == -1 
{
  var lo: int := 0 ;
  var hi: int := a.Length ;
  while (lo < hi)
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i : int :: (0 <= i < lo || hi <= i < a.Length) ==> a[i] != k
    invariant exists i: int :: (0 <= i < a.Length && a[i] == k)  ==> lo <= i <= hi
  { var mid: int := (lo + hi) / 2 ;
    if (a[mid] < k) {
      lo := mid + 1 ;
    } else if (a[mid] > k) {
      hi := mid ;
    } else {
      assert a[mid] == k;
      return mid ;
    }
  }
  return -1 ;
}