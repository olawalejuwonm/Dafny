// val b : ref bool
//  val x : ref int
//  let toy () : unit
//  requires { 0 <= !x <= 10 }
//  writes { b, x }
//  ensures { not !b }
//  ensures { !x <= 200 }
//  = b := false;
//  while (!x < 100) do
//  b := (!x < 50);
//  if !b then x := !x + 2
//  else x := !x + 3;
//  done;
//  assert { !x >= 75 }

method toy (xinit: int) returns (b: bool, x: int)
  requires 0 <= xinit <= 10
  ensures  !b
  ensures x <= 200
{
  b := false;
  x := xinit; // Local variable to hold the value of x
  while (x < 100)
    // invariant x >= 0 && x <= 200
    // invariant !b ==> x < 50
    // invariant b ==> x >= 50
  {
    b := (x < 50);
    if b {
      x := x + 2;
    } else {
      x := x + 3;
    }
    // b := (x < 50);
  }
  assert x >= 75;
}