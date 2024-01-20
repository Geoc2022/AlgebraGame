import Game.Levels.Group.L02_MulRight

World "Group"
Level 3

Title "Cancel Left Multiplication"

namespace MyAlgebra

Introduction "We now prove that we can cancel left multiplication. This is a bit more challenging than the previous two levels, but it will be helpful to know this later on. This is one half of the \"Cancellation Rule for Groups\""

/--
`mul_left_cancel` is a proof that if `h * g1 = h * g2`, then `g1 = g2` - the inverse of `mul_left` is a function.
-/
TheoremDoc MyAlgebra.mul_left_cancel as "mul_left_cancel" in "Group"
@[to_additive]
Statement mul_left_cancel (g : G) [Group G] : g * g1 = g * g2 → g1 = g2 := by
  intro h
  Hint "What can we do to get rid of the `g` on both sides? It might help to use a previous lemma."
  have q := mul_left g⁻¹ h
  Hint "The `g⁻¹` is bordered by `(` if it were `g` we could cancel"
  rw [←mul_assoc] at q
  rw [←mul_assoc] at q
  rw [inv_mul] at q
  rw [one_mul] at q
  rw [one_mul] at q
  exact q

Conclusion "Congrats!"
