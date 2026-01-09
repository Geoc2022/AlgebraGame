import Game.Levels.PowMonoid.L01_PowOne

World "Monoid Power"
Level 2

Title "Succ on the Left"

namespace MyAlgebra

Introduction "We know that `m ^ (n+1) = m ^ n * m`. In this level
you will show the equivalent statement with multiplication on the left:
`m ^ (n+1) = m * m ^ n`."

/--
For any monoid element `m`, `m ^ (n + 1) = m * m ^ n`.
-/
TheoremDoc MyAlgebra.mpow_succ_left as "mpow_succ_left" in "Monoid Power"
Statement mpow_succ_left {M} [Monoid M] (m : M) (n : ℕ) :
  m ^ (n + 1) = m * (m ^ n) := by
  induction n with
  | zero =>
    Hint "Start with the case `n = 0`."
    rw [Nat.zero_add, mpow_one]
    rw [mpow_zero, mul_one]
  | succ n ih =>
    Hint "Use the induction hypothesis and associativity."
    rw [mpow_succ_right]
    nth_rw 2 [mpow_succ_right]
    rw [ih, mul_assoc]

Conclusion "Good! You’ve learned to move the extra `m` to the left using induction and associativity."
