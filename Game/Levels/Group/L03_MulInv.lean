import Game.Levels.Group.L02_MulRight

World "Group"
Level 3

Title "Right Multiplicative Inverse"

namespace MyAlgebra

Introduction "We will now prove that we the inverse is a also a right multiplicative inverse. This is a bit more challenging than the previous two levels, but it will be helpful to know this later on. This is one half of the \"Cancellation Rule for Groups\""

/--
`mul_inv` is a proof that if `g` is an element of a group, then `g * g⁻¹ = 1`
-/
TheoremDoc MyAlgebra.mul_inv' as "mul_inv" in "Group"
Statement mul_inv' (g : G) [Group G] : g * g⁻¹ = 1 := by
  Hint "We have a similar lemma for the left inverse, can we use it here?"
  rw [←one_mul (g * _)]
  rw [←inv_mul (g⁻¹)]
  rw [mul_assoc]
  rw [←mul_assoc (g⁻¹)]
  rw [inv_mul]
  rw [one_mul]

Conclusion "Congrats!"
