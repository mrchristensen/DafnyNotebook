// Below is the familiar Dafny program for computing an absolute value of a number

method Abs(x : int) returns (y : int)
  ensures 0 <= y;
  ensures 0 <= x ==> y == x;
  ensures x < 0 ==> y == -x;
{
  if (x < 0)
   {y := -x;}
  else
   {y := x;}
}

// Use the weakest precondition calculus to prove that the program is correct with respect to the specification. Show the entire proof.