import Game.Levels.PowMonoid.L06_PowCommMul

World "Monoid Power"
Level 7

Title "Powers Commute with Powers"

namespace MyAlgebra

Introduction "Finally, you will prove the full statement:
`m ^ x * m ^ y = m ^ y * m ^ x`. We already know `m^x` commutes with `m`,
so we use induction to extend this to all powers."

/--
For any `m` in a monoid and naturals `x`, `y`,
`m ^ x * m ^ y = m ^ y * m ^ x`.
-/
TheoremDoc MyAlgebra.mpow_comm_mpow as "mpow_comm_mpow" in "Monoid Power"
Statement mpow_comm_mpow {M} [Monoid M] (m : M) (x y : ℕ) :
  (m ^ x) * (m ^ y) = (m ^ y) * (m ^ x) := by
  induction y with
  | zero => rw [mpow_zero, mul_one, one_mul]
  | succ y ih =>
    rw [mpow_succ_left]
    rw [mul_assoc]
    rw [← ih]
    rw [← mul_assoc m _ _]
    rw [← mul_assoc _ m _]
    rw [mpow_comm_mul]

Conclusion "Excellent work! You’ve proven a general version of the previous level - that all powers of an element commute with each other."
