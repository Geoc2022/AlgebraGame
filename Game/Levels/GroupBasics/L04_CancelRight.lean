import Game.Levels.GroupBasics.L03_CancelLeft

World "GroupBasics"
Level 4

Title "Cancel Right Multiplication"

namespace MyAlgebra
-- variable {α : Type} [Group α]

Introduction "We now prove that we can cancel right multiplication - the duel of the previous level. This is the second half of the \"Cancellation Rule for Groups\""

/--
`cancel_right` is a proof that if `g1 ⬝ g = g2 ⬝ g`, then `g1 = g2` - the inverse of `mul_right` is a function.
-/
TheoremDoc MyAlgebra.cancel_right as "cancel_right" in "Group"

Statement cancel_right (g : G) [Group G] : g1 ⬝ g = g2 ⬝ g → g1 = g2 := by
  intro h
  have q := mul_right (inv g) h
  rw [mul_assoc] at q
  rw [mul_inv] at q
  rw [mul_assoc] at q
  rw [mul_inv] at q
  rw [mul_one] at q
  rw [mul_one] at q
  exact q

Conclusion "Congrats!"
