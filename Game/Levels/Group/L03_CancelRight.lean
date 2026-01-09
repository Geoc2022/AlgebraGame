import Game.Levels.Group.L02_CancelLeft

World "Group"
Level 3

Title "Cancel Right Multiplication"

namespace MyAlgebra

Introduction "We now prove that we can cancel right multiplication - the duel of the previous level."

/--
`mul_right_cancel` is a proof that if `g1 * g = g2 * g`, then `g1 = g2` - the inverse of `mul_right` is a function.
-/
TheoremDoc MyAlgebra.mul_right_cancel as "mul_right_cancel" in "Group"
@[to_additive]
Statement mul_right_cancel (g : G) [Group G] : g1 * g = g2 * g → g1 = g2 := by
  intro h
  have q := mul_right (g⁻¹) h
  rw [mul_assoc] at q
  rw [mul_inv] at q
  rw [mul_assoc] at q
  rw [mul_inv] at q
  rw [mul_one] at q
  rw [mul_one] at q
  exact q

Conclusion "Congrats!"
