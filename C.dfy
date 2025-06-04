method count_1 (n:int) returns (r: int)
  requires n >= 0
{
  var i:int := 0;
  while (i<n)
  invariant  i <= n // This is not going to change after the loop termination 
  // The word invariant means “not changing” 
  // holds before the body of the loop is executed and
  // after the body of the loop is executed.
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