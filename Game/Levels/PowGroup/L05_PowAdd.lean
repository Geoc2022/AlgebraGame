import Game.Levels.PowGroup.L04_PowPred

World "Group Power"
Level 5

Title "Adding Integer Exponents"

namespace MyAlgebra

Introduction "Now you’ll prove the group version of the exponent-addition law:
`g ^ x * g ^ y = g ^ (x + y)` for all integers `x`, `y`."

/--
For any group element `g` and integers `x`, `y`,
`g ^ x * g ^ y = g ^ (x + y)`.
-/
TheoremDoc MyAlgebra.gpow_add as "gpow_add" in "Group Power"
Statement gpow_add {G} [Group G] (g : G) (x y : ℤ) :
  (g ^ x) * (g ^ y) = g ^ (x + y) := by
  Hint "Use `Int.induction_on` on `y`."
  induction y using Int.induction_on with
  | zero =>
    -- y = 0
    simp
  | succ y ih =>
    Hint "Use the recursive formula `gpow_succ` and associativity."
    simp [← Int.add_assoc, gpow_succ, ← ih, mul_assoc]
  | pred y ih =>
    Hint "Use `gpow_pred` for the negative step."
    rw [← gpow_pred]
    rw [← mul_assoc]
    rw [ih]
    rw [gpow_pred]
    rw [Int.add_sub_assoc]

Conclusion "Excellent! You have generalized the exponent addition law to all integers."
