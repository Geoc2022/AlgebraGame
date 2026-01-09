import Game.Levels.PowMonoid.L04_PowMul

World "Monoid Power"
Level 5

Title "Powers of the Identity"

namespace MyAlgebra

Introduction "Now show that the identity element is fixed under taking powers:
`1 ^ x = 1`."

/--
For any monoid, `1 ^ x = 1` for all `x : ℕ`.
-/
TheoremDoc MyAlgebra.mpow_id as "mpow_id" in "Monoid Power"
Statement mpow_id {M} [Monoid M] (x : ℕ) : (1 : M) ^ x = 1 := by
  induction x with
  | zero =>
    Hint "What is `1^0` by definition?"
    rw [mpow_zero]
  | succ x ih =>
    Hint "Use the recursive definition of pow and the fact that `1 * 1 = 1`."
    rw [mpow_succ_right, ih, mul_one]

Conclusion "Nice! Identity behaves as expected under exponentiation."
