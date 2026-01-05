import Game.Levels.Group.L06_OneUnique

World "Group"
Level 7

Title "Unique Inverse"

namespace MyAlgebra

Introduction "Similar to how there's only one identity element, there's only one inverse element. We can use a similar augment from the last level to prove this. If `i` and `g⁻¹` are both inverses of `g`, then `i = g⁻¹`."

/--
`inv_unique` is a proof that there is only one inverse element in a group for any given element.
-/
TheoremDoc MyAlgebra.inv_unique as "inv_unique" in "Group"
-- @[to_additive]
Statement inv_unique (g i : G) [Group G] (h : g * i = (1 : G) ∧ i * g = (1 : G)) : i = g⁻¹ := by
  rw [←mul_one g⁻¹]
  rw [←h.1]
  rw [← mul_assoc]
  rw [inv_mul]
  rw [one_mul]

Conclusion "Congrats!"
