// The factorial function, n! computes the product of all numbers from 1 up to n (e.g., 3! = 1 * 2 * 3 = 6). The following Dafny program iteratively calculates the factorial of a number.

method ComputeFact(n : nat) returns (res : nat)
requires n > 0;
ensures res == fact(n);
{
  res := 1;
  var i := 2;
  while (i <= n)
  {
    res := res * i;
    i := i + 1;
  }
}
 ```

// The variables are natural numbers. Prove that the program is correct with respect to the following recursive definition:
// fact(1) = 1 fact(m) = m * fact(m - 1) ```

// Part A: Complete the specification so that Dafny is able to prove ComputeFact correct relative to the specification.

// Part B: Construct a paper-pencil proof of total correctness of the loop.