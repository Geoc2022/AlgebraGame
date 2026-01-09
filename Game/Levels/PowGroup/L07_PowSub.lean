import Game.Levels.PowGroup.L06_PowNeg

World "Group Power"
Level 7

Title "Subtracting Integer Exponents"

namespace MyAlgebra

Introduction "We now prove the exponent law for subtraction:
multiplying by the inverse of `g ^ y` corresponds to subtracting `y` in the exponent."

/--
For any group element `g` and integers `x`, `y`, we have
`g ^ x * (g ^ y)⁻¹ = g ^ (x - y)`.
-/
TheoremDoc MyAlgebra.gpow_sub as "gpow_sub" in "Group Power"
@[simp]
Statement gpow_sub {G} [Group G] (g : G) (x y : ℤ) :
    (g ^ x) * (g ^ y)⁻¹ = g ^ (x - y) := by
  Hint "Recall that `x - y = x + (-y)`."
  Hint "Try rewriting `x - y` using `sub_eq_add_neg` and then apply the addition rule `gpow_add` and the negation rule `gpow_neg`."
  -- First rewrite subtraction as addition with a negative exponent:
  rw [sub_eq_add_neg]
  -- Now use the addition and negation lemmas:
  rw [← gpow_add]
  rw [gpow_neg]

Conclusion "Nice! You’ve shown that a negative exponent in the second factor corresponds to subtracting exponents."
