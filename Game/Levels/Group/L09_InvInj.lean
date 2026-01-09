import Game.Levels.Group.L07_InvId

World "Group"
Level 9

Title "Inverse is Injective"

namespace MyAlgebra

Introduction "
  Since the inverse of an inverse to be the original element it follows that if two elements have the same inverse, they must be equal.
"

/--
`inv_inj` is a proof that the inverse is injective.
-/
TheoremDoc MyAlgebra.inv_inv as "inv_inj" in "Group"
@[to_additive]
Statement inv_inj (a b : G) [Group G] : a⁻¹ = b⁻¹ ↔ a = b := by
  apply Iff.intro
  · intro h
    calc a = a := by rfl
      _ = a * 1 := by rw [mul_one]
      _ = a * (b⁻¹ * b) := by rw [inv_mul]
      _ = (a * b⁻¹) * b := by rw [mul_assoc]
      _ = (a * a⁻¹) * b := by rw [← h]
      _ = 1 * b := by rw [mul_inv]
      _ = b := by rw [one_mul]
  · intro h
    rw [h]

Conclusion "Congrats!"
