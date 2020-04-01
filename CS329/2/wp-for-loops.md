# Objectives

   * Prove partial correctness of simple loops (assumes the loop terminates)
   * Prove full correctness of simple loops (proves termination)

# Reading

   * [Formal Verification 2](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/chalmers-slides/FormalVerification2.pptx) or [chalmers](http://www.cse.chalmers.se/edu/year/2016/course/course/TDA567_Testing_debugging_and_verification/Lectures/FormalVerification1/FormalVerification1.html)
   * [The Science of Programming](http://www.cs.cornell.edu/gries/July2016/The-Science-Of-Programming-Gries-038790641X.pdf)

# WP Rules Summary and Proof

`Q` is a post-condition. The notation `Q[x -> e]` means to replace every occurrence of `x` in `Q` with `e`. 

   * `wp({}, Q) = Q`
   * `wp(s1;s2, Q) = wp(s1, wp(s2, Q))`
   * `wp(x := e, Q) = Q[x -> e]`
   * `wp(assert X, Q) = X /\ Q`
   * `wp(if E {A} else {B}, Q) = (E /\ wp(A, Q)) \/ (!E /\ wp(B,Q))` (reduced form from simplifying the implication of `(E ==> wp(A, Q)) /\ (!E ==> wp(B,Q))` )

`wp` is computable for these constructs (i.e., decidable): see [weakest-precondition.md](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/weakest-preconditions.md) for examples and more explanation.

**Proof** in this context means that it is possible to prove the post-condition holds given the pre-condition. Consider the invariant below for the simple program.

   * Compute `wp(R,Q)` using the WP Rules
   * Show that `P ==> wp(R,Q)`

In the absence of loops, everything is done sort-of: it assumes termination!

   * **Partial Correctness**: assume the program terminates and prove correctness
   * **Total Correctness**: prove programs with loops (or recursion) without the termination assumption (prove loops terminate too)

Focus on partial correctness first and dealing with loops.

# WP For Loops

`wp(while E {A}, Q)` is not computable (halting problem) and no algorithm exists compute it correctly on all inputs. Provide an invariant that can be used to try to compute the weakest precondition:

**Loop invariant**: predicate that is true after *any number* of iterations of the loop including zero. The invariant is useful if it enables the proof of the program. See [dafny/Simple-Loop.dfy](dafny/Simple-Look.dfy).

```java
method simpleInvariant(n : int) returns (m : int)
requires n >= 0
ensures  n == m {
  m := 0; // 1
  while m < n 
  decreases n-m;
  invariant m <= n
  { 
    m := m + 1; // 3 
  } // 2
}
```

Note that it is not just `m < n` because it must be true after any number of iterations. On loop exit, `m == n`.

Computing `wp(while E I S, Q)` for partial correctness consists of showing that

   * `I`: invariant holds *before* the loop
   * `(E /\ I ==> wp(S,I))`: If the invariant holds before the loop then it must hold after the loop body on an iteration
   * `(!E /\ I ==> Q)`:  If the loop invariant holds and the loop exits, then it must satisfy the post-condition.

The post-condition `Q` comes from the normal *WP Rules* (above) and the loop-addition here as needed. The general proof structure for partial correctness proceeds by computing the `wp` for the program, `S`, and showing that given the requires `R` that `R ==> wp(S,Q)`.

It is possible to further simplify computing `wp(while E I S, Q)` with factoring:

   * `I`: invariant holds *before* the loop
   * `(E ==> wp(S,I))`: If the invariant holds before the loop then it must hold after the loop body on an iteration
   * `(!E ==> Q)`:  If the loop invariant holds and the loop exits, then it must satisfy the post-condition.

Work in detail the proof for **simpleInvariant** above (see [Simple-Loop.dfy](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/dafny/Simple-Loop.dfy)). Use a recursion tree to organize the proof an show how the `wp` computation flows up from the bottom of recursion. The control-flow-graph can be helpful as well to keep track of flow going down the recursion and then back up.

# Termination Proofs

Prove partial correctness on the following:

```java
method magic returns ()
requires true;
ensures 1 == 0;
{
   while (1 != 0) 
   invariant true
   {}
}
```

The proof says the above is correct, but that is dumb as the ensures can never be true. Ever! The issue is that the proof assumes termination and method `magic` breaks that assumption.

Proving termination is also not computable in general, but can be done for many input programs. Dafny uses the decreases clause `D` and shows two things:

   1. `D >= 0` always.
   2. `D` decreases on each iteration of the loop.

The decreases clause should be similar to the invariant meaning that it is bounded below by zero an any number of iterations of the loop, so you have to think carefully about `i <= n` for example, since a decreases of `n-i` would not be bounded below by zero when the loop exits! In such cases, `n+1-i` would be more appropriate.

Computing `wp(while E I S, Q)` for total correctness consists of showing that

   * `I`: invariant holds *before* the loop
   * `(E ==> wp(S,I))`: If the invariant holds before the loop then it must hold after the loop body on an iteration
   * `(!E ==> Q)`:  If the loop invariant holds and the loop exits, then it must satisfy the post-condition.
   * `I ==> D >= 0`: the decrease expression bounded below by zero (may be strengthened to only hold on each iteration of the loop but shouldn't need to be strengthened in general)
   * `(E ==> wp(S, old(D) > D))`: the decrease expression decreases on each iteration (*old* is the Dafny keyword)

The post-condition `Q` comes from the normal *WP Rules* (above) and the loop-addition here as needed. Note that it is possible to combine the second and third bullets to `(E /\ I ==> wp(S,I /\ old(D) < D))`. Keep track of `old(D)` with a temporary variable inserted into the `wp` calculation: `wp(t := D; S, t > D)`. Here is a more compact statement of the obligations with the computation for `old(D)` added in:

   * `I`
   * `E ==> (wp(S,I) && wp(t := D; S, tmp > D))`
   * `!E ==> Q`
   * `D >= 0`

Remember that `t` must be some free variable. Prove the additional obligations for `SimpleInvariant`. Prove `n >= 1 ==> wp(Fib, c == fib(n))`

```java
function fib(n : nat) : nat
{ if n <= 1 then n else fib(n-1) + fib(n - 2) }

method fibFast(n : nat) returns (c : nat)
requires n >= 1
ensures c == fib(n)
{ 
  var p := 0; // 1
  c  := 1; // 2
  var i := 1; // 3
  while i < n
  invariant 1 <= i <= n
  invariant p == fib(i - 1) && c == fib(i)
  decreases (n - i)
  { var t := p + c; // 5
    p := c; // 6
    c := t; // 7
    i := i + 1; // 8
  } // 4
}
```

See [wp-loops-examples.pdf](wp-loops-examples.pdf).

# Loop Examples

All the solutions have the **sol** at the end of the name. Several are in [wp-loops-examples.pdf](wp-loops-examples.pdf).

   * [SimpleLoop2.dfy](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/dafny/SimpleLoop2.dfy)
   * [fib.dfy](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/dafny/fib.dfy)
   * [Division.dfy](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/dafny/Division.dfy)
   * [HashTable.dfy](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/dafny/HashTable.dfy)
   * [verify-m3.dfy](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/dafny/verify-m3.dfy)
   * [verify-m4.dfy](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/dafny/verify-m4.dfy)
   * [verify-m5.dfy](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/dafny/verify-m5.dfy)