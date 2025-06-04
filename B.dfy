method TwoX(x: int) returns (y: int)
  requires x == 0 || x == 2 || x == 6
  ensures y == 2 * x
{
  y := 0;
  if (x == 2) {y := 4;}
  if (x == 6) {y := 12;}
}




// calling the method
method Main()
{
  var a := 0;
  var b := 2;
  var c := 6;

  var res1 := TwoX(a); // should return 0
  print res1;
  print " Expected: 0 ";
  
  var res2 := TwoX(b); // should return 4
  print res2;
  print " Expected: 4 ";
  
  var res3 := TwoX(c); // should return 12
  print res3;
  print " Expected: 12 ";
}