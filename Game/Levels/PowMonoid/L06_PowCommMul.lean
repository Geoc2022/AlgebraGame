import Game.Levels.PowMonoid.L05_PowId

World "Monoid"
Level 6

Title "Commuting a Power with its Base"

namespace MyAlgebra

Introduction "In a general monoid, `m` need not commute with all elements, but
it does commute with its own powers. You’ll prove `m ^ x * m = m * m ^ x`."

/--
For any `m` in a monoid and `x : ℕ`,
`m ^ x * m = m * m ^ x`.
-/
TheoremDoc MyAlgebra.mpow_comm_mul as "mpow_comm_mul" in "Monoid"
Statement mpow_comm_mul {M} [Monoid M] (m : M) (x : ℕ) :
  (m ^ x) * m = m * (m ^ x) := by
  induction x with
  | zero =>
    Hint "Start with `x = 0`."
    rw [mpow_zero, one_mul, mul_one]
  | succ x ih =>
    Hint "Rewrite `m^(x+1)` and use associativity plus the induction hypothesis."
    nth_rw 1 [mpow_succ_left, mpow_succ_right]
    simp [ih, mul_assoc]

Conclusion "Great!"
