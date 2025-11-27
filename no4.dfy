method find_max (a: seq<int>) returns (m: int)
  requires |a| >= 1
  ensures forall j : int :: 0 <= j < |a| ==> a[j] <= m
{   
   var i := 1; m := a[0];
   while (i < |a|) 
      invariant 1 <= i <= |a|
      invariant forall k :: 0 <= k < i ==> a[k] <= m
   {
      if a[i] >= m
        {m:=a[i];}
      i := i + 1;
   }
}

function exp_spec(b: int, e: int): int
requires (e >= 0)
{ 
  if (e<=0) then 1
  else b * exp_spec(b, e-1)
}

method fast_exp(n: int) returns (r: int)
  requires n >= 0
  ensures r == exp_spec(2, n)
{ var e: int := n; // exponent 
  var b: int := 2; // base
  r := 1; // result
  while (e > 0) 
  invariant e >= 0
  invariant e <= (n)
  invariant r == exp_spec(2, (e / 2))
  {
      if (e % 2 == 1)
      {
        r := b * r;
        e := e - 1;
      }
      e := e / 2;
      b := b * b;
  }
  return r;
}

method nodup(a: seq<int>) returns (b: bool)
   ensures b <==> forall i: int, j : int :: 0<=i<j<|a|==>a[i]!=a[j]
{
  b := true; 
  var m := |a| - 1;
  while (m > 0) 
  {
    var n := m-1;
    while (n >= 0)
    {
      if a[n]==a[m]
         {b:= false;}
       n := n - 1; 
    }
    m := m - 1; 
  }
}