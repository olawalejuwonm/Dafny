// Integer square root algorithms
// based on Wikipedia
// https://en.wikipedia.org/wiki/Integer_square_root
// The presented C programs have been adapted to Dafny by Markus Roggenbach

// For an integer y >=0, the function isqrt(y) is defined to be the
// integer x with x * x <= y < (x+1) * (x+1)

// Each method implements a different algorithm for solving this problem.

// Integer square root (using linear search, ascending)
method SquareRootAscendingSearch(y: int) returns (result: int)
  requires y >= 0
  ensures result * result <= y < (result+1) * (result+1)
{
  // initial underestimate, L <= isqrt(y)
  var L: int := 0;

  while ((L + 1) * (L + 1) <= y)

    /* invariant hint: uncomment the next line and use invariant design principle 2,
       applied to the left inequality of the "ensures".
    */
    // invariant <PUT YOUR INVARIANT HERE>
    invariant L * L <= y

  {
    L := L + 1;
  }
  result := L;
}

// Integer square root (using linear search, descending)
method SquareRootDescendingSearch(y:int) returns (result: int)
  requires y >= 0
  ensures result * result <= y < (result+1) * (result+1)
{
  // initial overestimate, isqrt(y) <= R
  var R: int := y;

  while (R * R > y)

    /* invariant hint: uncomment the next line and use invariant design principle 1,
       relating zero and R to deal with loop termination.
    */
    invariant R >= 0 && (R <= R * R)

    /* invariant hint: uncomment the next line and use invariant design principle 2,
       applied to the right inequality of the "ensures".
    */
    invariant  ((R+1)*(R+1)) > y

  {
    R := R - 1;
  }
  result := R;
}

// Integer square root
// (linear search, ascending) using addition
method SquareRootAscendingUsingAddition(y: int) returns (result: int)
{
  var L: int;
  var a: int;
  var d: int;
  L := 0;
  a := 1;
  d := 3;

  // No loop invariant is needed as Dafny is clever enough in this case.
  while (a <= y)
  {
    a := a + d;
    d := d + 2;
    L := L + 1;
  }

  result := L;
}

// Integer square root (using binary search)
method SquareRootBinarySearch(y: int) returns (result: int)
  requires y >= 0
  ensures result * result <= y 
{
  var L: int; // Lower bound
  var M: int; // Middle value
  var R: int; // Upper bound

  L := 0;
  R := y+1;
  M := (L + R) / 2;

  while (L != R - 1)

    /* invariant hint: uncomment the next line and use invariant design principle 1,
       relating L and M to partially deal with loop termination.
    */
    // invariant <PUT YOUR INVARIANT HERE>
    //  invariant L <= M * M
    invariant L <= R


    //   invariant R >= 1
    //  invariant L >= y
    invariant R > L

    /* invariant hint: uncomment the next line and use invariant design principle 1,
       relating M and R to partially deal with loop termination.
    */
    //  invariant !(R < M+y+1)
    // invariant  R >= L
    // invariant R >=  M
    /* invariant hint: uncomment the next line and use invariant design principle 2,
       relating L and y applied to the left inequality of the "ensures".
    */
    //  invariant L * L <= y

    /* invariant hint: uncomment the next line and use invariant design principle 2,
       relating L and y applied to the right inequality of the "ensures".

       Hint: As the upper bound of the loop condition deals with (R - 1),
             the original right inequality of "ensures" will be 1 too large.
    */
    //  invariant (y) < (L+R) * (L+R)
    //  invariant (y) < ((L + 1) * (L + 1))

    invariant L * L <= y

    //  invariant (y) < ((L+1) * (L+1) + y + 1)
    // invariant (y) <= ((L+1) * (L+1) + y)

    // invariant (y) < ((L+1) * (L+1)   + y)



    // < (L+1) * (L+1)

    //  invariant L >= 0
    //  invariant L <= M
  {
    M := (L + R) / 2;
    if (M * M <= y)
    { L := M; }
    else
    { R := M;}
  }

  result := L;
}