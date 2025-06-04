method count_1 (n:int) returns (r: int)
  requires n >= 0
{
  var i:int := 0;
  while (i<n)
  invariant  i <= n // This is not going to change after the loop termination
  {
    i := i + 1;
  }
  assert i >= n;
  // assert i > n;
  // assert i < n;
  assert i == n;
  // assert i == n;
  r := 0;
}