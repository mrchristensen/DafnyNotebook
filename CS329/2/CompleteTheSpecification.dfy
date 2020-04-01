// Below is a small Dafny program

method Q2(x : int, y : int) returns (big : int, small : int)
  ensures big > small;
{
  if (x > y)
   {big, small := x, y;}
  else
   {big, small := y, x;}
}

// Part A: Dafny will not be able to prove the above program correct because its specification is incomplete. Figure out exactly why the proof fails, and from there derive the missing part of the specification. Changing the postcondition or method body in not allowed; rather, use weakest precondition calculus to find a suitable pre-condition. Show each step of the derivation.

// Part B: Show that your answer from Part A enables Dafny to prove the program correct.