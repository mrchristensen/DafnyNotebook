//The other situation that requires a termination proof is when methods or functions are recursive. Similarly to looping forever, these methods could potentially call themselves forever, never returning to their original caller. When Dafny is not able to guess the termination condition, an explicit decreases clause can be given along with pre- and postconditions, as in the unnecessary annotation for the fib function:

function fib(n: nat): nat
   decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}
