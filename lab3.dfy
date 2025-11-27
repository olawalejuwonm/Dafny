method Distance(x: int, y: int) returns (z: int)
  requires x > 0
  requires y > 0
  ensures z == y-x
{
  z := y - x;
}

method Order(x: int, y: int, z: int) returns (result: int)
  ensures result == 1 || result == -1 || result == 0
{
  if z > y && y > x {
    result := 1;
  }
  else if x > y && y > z {
    result := -1;
  }
  else {
    result := 0;
  }

}

//  1 3 3 
//  4 5 5 
//  6 6 6 2
// the program should print 3 5 6.

method AdjDuplicate(x: array<int>) returns (result: seq<int>)
requires x.Length > 2
ensures forall i | 0 <= i < result.Length - 1 { result[i + 1] > result[i] }
{
  result := [];
  for i := 0 to x.Length - 2 {
    if x[i] == x[i+1] {
      result := result + [x[i]];
    }
  }
}