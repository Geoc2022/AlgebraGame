import Game.Levels.GroupBasics.L08_CombinedInv2

World "GroupBasics"
Level 9

Title "Inverse of an Inverse"

namespace MyAlgebra

Introduction "
  You would expect the inverse of an inverse to be the original element. Ex. `-(-2) = 2` or the composition of two flips is the identity. But let's formally prove it.
"

/--
`inv_inv` is a proof that the inverse of an inverse is the original element.
-/
TheoremDoc MyAlgebra.inv_inv as "inv_inv" in "Group"
@[to_additive]
Statement inv_inv (a : G) [Group G] : a⁻¹⁻¹ = a := by
  have h : a⁻¹⁻¹ * a⁻¹ = 1 := by
    rw [inv_mul]
  have h2 : (a⁻¹⁻¹ * a⁻¹) * a = 1 * a := by
    rw [h]
  have h3 : a⁻¹⁻¹ * (a⁻¹ * a) = a := by
    rw [one_mul] at h2
    rw [mul_assoc] at h2
    exact h2
  rw [inv_mul] at h3
  rw [mul_one] at h3
  exact h3

Conclusion "Congrats!"
