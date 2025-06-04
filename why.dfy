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
  requires 0 <= xinit <= 10  // precondition for xinit
  ensures  b == false // postcondition ensures b is false at the end
  ensures x <= 200 // postcondition ensures x is at most 200
{
  b := false;
  x := xinit; // Local variable to hold the value of x

  while (x < 100)
    invariant ((b == false && 0 <= x && x <= 10) || (b == true && 2 <= x && x <= 51) || (b == false && 53 <= x && x <= 102))
  {
    b := (x < 50);
    if (b == true) {
      x := x + 2; // evaluate this first since x < 50
    } else {
      x := x + 3;
    }
  }
  assert x >= 100;
  assert x >= 75;
}