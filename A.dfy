method Mult (x: int, y: int) returns (result: int)
  ensures (y == 1) ==> result == x
  ensures (y == 0) ==> result == 0
  ensures (x > 0 && y > 0) ==> result > 0
  ensures ((x > 0 && y < 0) || (y > 0 && x < 0) )
          ==> result < 0
{
  result := x * y ;
}

// calling the method
method Main()
{
  var a := 5;
  var b := 3;
  var c := -2;
  var d := 0;

  var res1 := Mult(a, b); // should return 15
  print res1;
  print " Expected: 15";
  var res2 := Mult(a, c); // should return -10
  print res2;
  print " Expected: -10";
  var res3 := Mult(a, d); // should return 0
  print res3;
  print " Expected: 0";
  var res4 := Mult(b, c); // should return -6
  print res4;
  print " Expected: -6";

}
