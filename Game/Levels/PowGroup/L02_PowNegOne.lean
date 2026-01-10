import Game.Levels.PowGroup.L01_PowNegNat

World "Group Power"
Level 2

Title "The Inverse: g⁻¹ = g^(-1)"

namespace MyAlgebra

Introduction "Here you show that exponent `-1` gives the group inverse."

/--
For any group element `g`, we have `g ^ (-1) = g⁻¹`.
-/
TheoremDoc MyAlgebra.gpow_neg_one as "gpow_neg_one" in "Group Power"
Statement gpow_neg_one {G} [Group G] (g : G) :
  g ^ (-1) = g⁻¹ := by
  Hint "Write `-1` as `-(1 : ℤ)` and then use the previous level."
  have : (1 : ℤ) = (1 : ℕ) := rfl
  -- or simply: `rw [← Int.ofNat_one]`
  rw [← Int.ofNat_one, gpow_neg_mpow]
  simp

Conclusion "Now you see that the usual inverse `g⁻¹` is just `g` raised to `-1`."
