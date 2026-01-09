import Game.Levels.PowMonoid.L03_PowAdd

World "Monoid Power"
Level 4

Title "Multiplying Exponents"

namespace MyAlgebra

Introduction "Next, you will prove another standard law: `m ^ (x * y) = (m ^ x) ^ y`."

/--
For any `m` in a monoid and naturals `x`, `y`, `m ^ (x * y) = (m ^ x) ^ y`.
-/
TheoremDoc MyAlgebra.mpow_mul as "mpow_mul" in "Monoid Power"
Statement mpow_mul {M} [Monoid M] (m : M) (x y : ℕ) :
  m ^ (x * y) = (m ^ x) ^ y := by
  induction y with
  | zero =>
    Hint "Start with `y = 0` first."
    -- m^(x*0) = m^0 = 1, and (m^x)^0 = 1
    simp [Nat.mul_zero, mpow_zero]
  | succ y ih =>
    Hint "Use the `mpow_add` lemma from the previous level."
    -- m^(x*(y+1)) = m^(x*y + x) = m^(x*y) * m^x
    -- and (m^x)^(y+1) = (m^x)^y * m^x
    simp [Nat.mul_succ, mpow_add, mpow_succ_right, ih]

Conclusion "Well done! You have derived the law of exponents for multiplication. Can you think of any examples of this law?"
