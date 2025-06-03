import Game.Levels.Group.L08_CombinedInv2

World "Group"
Level 9

Title "Inverse of an Inverse"

namespace MyAlgebra

Introduction "
  You should expect the inverse of an inverse to be the original element. Ex. `-(-2) = 2` or the composition of two flips is the identity. But let's formally prove it.
"

/--
`inv_inv` is a proof that the inverse of an inverse is the original element.
-/
TheoremDoc MyAlgebra.inv_inv as "inv_inv" in "Group"
@[to_additive]
Statement inv_inv (a : G) [Group G] : a = a⁻¹⁻¹ := by
  calc a = a := by rfl
    _ = a⁻¹⁻¹ * a⁻¹ * a := by
      rw [inv_mul]
      rw [one_mul]
    _ = a⁻¹⁻¹ * (a⁻¹ * a) := by
      rw [mul_assoc]
    _ = a⁻¹⁻¹ * 1 := by
      rw [inv_mul]
    _ = a⁻¹⁻¹ := by
      rw [mul_one]

Conclusion "Congrats!"
