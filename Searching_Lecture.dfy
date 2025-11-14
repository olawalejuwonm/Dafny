method Search (a: array<int>, k: int) returns (index: int)
   ensures   exists i: int :: (0 <= i < a.Length && a[i] == k)  ==> index == i
   ensures !(exists i: int :: (0 <= i < a.Length && a[i] == k)) ==> index == -1 
{
  var l: int := 0;
  while (l < a.Length && a[l] != k) 
    invariant 0 <= l <= a.Length
    invariant forall i: int :: (0 <= i < l ==> a[i] != k) 
  {
     l := l + 1;
  }
  if l < a.Length { index := l; }
  else { index := -1;}
} 