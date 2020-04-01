# Intro

This lecture took two class periods. We have not yet arrived at a notation that clearly works for students. The notation in this document will be chained and nested Hoare triples.

The [slides from Chalmers](chalmers-slides/FormalVerification1.pdf) are likely the clearest. The [ANU slides](19wp1.pdf) make some aspects clearer but are more dense.

# Reading

   * [Predicate Transformer Semantics](https://en.wikipedia.org/wiki/Predicate_transformer_semantics)
   * [Weakest Precondition Calculus](https://cs.anu.edu.au/courses/comp2600/Lectures/19wp1.pdf)
   * [Formal Verification 1](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/chalmers-slides/FormalVerification1.pptx) or [chalmers](http://www.cse.chalmers.se/edu/year/2016/course/course/TDA567_Testing_debugging_and_verification/Lectures/FormalVerification1/FormalVerification1.html)
   * [The Science of Programming](http://www.cs.cornell.edu/gries/July2016/The-Science-Of-Programming-Gries-038790641X.pdf)
   * [Hoare Logic](https://www.cs.cmu.edu/~aldrich/courses/413/slides/24-hoare.pdf) or [Hoare 2](https://www3.risc.jku.at/education/oldmoodle/file.php/22/slides/02-hoare.pdf)
   * [Forward Derivation with Strongest Post-condition](http://www2.informatik.uni-freiburg.de/~heizmann/ProgramVerification/slides/20111128-Mon-ForwardDerivation.pdf)

# Background

First, we need to establish notation for Hoare triples. Following the convention from the Chalmers slides, we write a triple as:

    {Q} S {R} .

This states that if `Q` is the case before `S` executes, that `S` will terminate (without generating an error state) and that `R` will be true after `S` completes.

For example,

    {} x = 3 {x == 3}

is a Hoare triple.

This is relational; `Q` may strengthen and `R` may weaken arbitrarily and the resulting Hoare triple will still be true. Accordingly,

    {y == 2} x = 3 {x == 3}

strengthens the precondition and is still true. Similarly,

    {} x = 3 {}

weakens the postcondition and is still true.

# Outline for 2019

See [wp-examples.pdf](wp-examples.pdf). The examples use a recursion tree to show how to recurse to the end of a program and then compute the weakest pre-condition on the way out of recursion. The examples build in complexity and introduce each rule at a time. Students should work the last example. It illustrates why if-statements have to first compute to the end of the program before computing the weakest-precondition for each branch. **Note**: always bottom-out to an empty-statement to return the original post-condition.

For each example, prove that `true --> wp` for the program. If that is not strong enough to be a tautology, then strengthen the pre-condition to complete the proof. The goal is to connect the contract to the verification. The pre-condition should be strong enough to imply the weakest-precondition for the program given the postcondition.

# Proving Correctness in the absence of loops

A program `S` given pre-conditions `P` and post-conditions `Q` is proven correct if and only if `P ==> wp(S,Q)`. In other words, if the pre-condition implies the weakest precondition for the program, then the program is correct relative to its contract.

# Weakest preconditions

In contrast, we can compute the unique weakest precondition for which a Hoare triple may be constructed, given a statement and a postcondition. For our running example,

    wp(x = 3, x == 3) = {3 == 3} = {} .

Since 3 is always equal to itself, an empty precondition is sufficient. This is the weakest possible precondition for this case.

## Assignments

We can create general rules for weakest preconditions, just as we did for type proofs. An assignment always terminates (assuming that computing the value of its expression terminates normally and that the lvalue in question may be assigned), so the only thing that must be proven is that the postcondition will be satisfied.

The postcondition, of course, may read from the lvalue modified in the assignment. As such, the postcondition must be modified so that it references the rvalue of the assignment instead of the lvalue:

    wp(x = e, R) = R[x <- e] .

## Sequencing

This is perhaps the most satisfying of the rules. In some sense, we want to chain preconditions and postconditions together when faced with sequenced statements (e.g., `S; T`):

    {P} S {Q} T {R} .

In this example, `Q` is both the postcondition to `S` and the precondition to `T`. More formally, we can compute the weakest precondition of `T` that satisfies `R` and then use that result as the postcondition for `S`:

    wp(S; T, R) = wp(S, wp(T, R)) .

## Branching

A simple if/then/else statement presents a more complicated case for formal verification. In this case, we must reason about both branches. If the condition is true, then we need a precondition that guarantees that execution of the true branch will result in the postcondition being true. If the condition is false, we need a precondition that guarantees that execution of the _false_ branch will result in the same postcondition being true.

One can argue for either of the following two forms as most intuitive:

    wp(if (c) t else f, R) =
        c => wp(t, R) && !c => wp(f, R)

or

    wp(if (c) t else f, R) =
        (c && wp(t, R) || (!c && wp(f, R)) .

It is worthwhile and interesting to explore a proof that these two are equivalent. A truth table is sufficient but a Karnaugh map is much more satisfying.

# Dafny

The weakest precondition calculus is how Dafny operates. It computes a function's postcondition by conjoining its `ensures` clauses. Then, it computes the weakest precondition of the body (remember that the body is a sequence of statements and we have a sequencing rule). Lastly, it ensures that the precondition stated in the `requires` clauses implies the computed weakest precondition. If that implication is true, the function has been verified.

# Examples

Work through small examples, such as the ones on slide 23.1 of the Chalmers slides. Also, work through examples like `guess()` in the [Dafny code](dafny/Secret-sol.dfy).

# WP Summary and Practice Problems

`Q` is a post-condition. The notation `Q[x <- e]` means to replace every occurrence of `x` in `Q` with `e`. The more common notation is `Q[e/x]` that means that every free occurrence of `x` in `Q` is replaced by `e`. 

   * `wp({}, Q) = Q`
   * `wp(x := e, Q) = Q[x <- e]`
   * `wp(assert X, Q) = X /\ Q`
   * `wp(s1 ; s2, Q = wp(s1, wp(s2, Q))`
   * `wp(if E {A} else {B}, Q) = (E /\ wp(A, Q)) \/ (!E /\ wp(B,Q))` (reduced form from simplifying the implication of `(E ==> wp(A, Q)) /\ (!E ==> wp(B,Q))` )

`wp` is computable for these constructs (i.e., decidable). Examples to work:

  * Practice [dafny/verify-m1.dfy](dafny/verify-m1.dfy)
  * Write and prove an implementation that satisfies `ensures: (m = a || m = b || m = c) && (m <= a && m <= b && m <= c)` ([dafny/verify-m2.dfy](dafny/verify-m2.dfy))
