import Game.Levels.PowMonoid.L02_PowSuccLeft

World "Monoid Power"
Level 3

Title "Adding Exponents"

namespace MyAlgebra

Introduction "Now we prove the fundamental law of exponents in a monoid:
`m ^ (x + y) = m ^ x * m ^ y`."

/--
For any `m` in a monoid and natural numbers `x`, `y`, we have `m ^ (x + y) = m ^ x * m ^ y`.
-/
TheoremDoc MyAlgebra.mpow_add as "mpow_add" in "Monoid Power"
Statement mpow_add {M} [Monoid M] (m : M) (x y : ℕ) :
  m ^ (x + y) = (m ^ x) * (m ^ y) := by
  induction y with
  | zero =>
    Hint "Start with `y = 0`."
    -- m^(x+0) = m^x and m^x * m^0 = m^x * 1
    simp [Nat.add_zero, mpow_zero]
  | succ y ih =>
    Hint "Use the recursive definition of pow and the induction hypothesis."
    -- m^(x + (y+1)) = m^(x + y + 1) = m^(x+y)*m
    -- and (m^x * m^y) * m = m^x * (m^y * m)
    rw [Nat.add_succ, mpow_succ_right, ih]
    rw [mpow_succ_right]
    rw [mul_assoc]

Conclusion "Awesome! You have the exponent law for addition"
