// The following method multiplies two integers.

method Q3(n0 : int, m0 : int) returns (res : int)
{
  var n, m : int;
  res := 0;
  if (n0 >= 0)
       {n,m := n0, m0;}
  else
       {n,m := -n0, -m0;}
  while (0 < n)
  {
    res := res + m;
    n := n - 1;
  }
}

// n0 and m0 are the two integer inputs to the program copied into the local variables n and m respectively because Dafny does not allow the re-assignment of formal parameters. res is the integer result.

// Part A: Write a specification for the above method and show that Dafny is able to prove total correctness relative to the specification. Use weakest-precondition calculus as needed to create the specification.

// Part B: Construct a paper-pencil proof of the method showing all five obligations required to compute the weakest-precondition for the loop for total correctness.