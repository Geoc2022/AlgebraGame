import Game.Levels.GroupBasics.L08_CombinedInv2

World "GroupBasics"
Level 9

Title "Inverse of an Inverse"

namespace MyAlgebra
-- variable {α : Type} [Group α]

Introduction ""

/--
`inv_inv` is a proof that the inverse of an inverse is the original element.
-/
TheoremDoc MyAlgebra.inv_inv as "inv_inv" in "Group"
Statement inv_inv (a : G) [Group G] : a⁻¹⁻¹ = a := by
  have h : mul (inv (inv a)) (inv a) = one := by
    rw [inv_mul]
  have h2 : mul (mul (inv (inv a)) (inv a)) a = mul one a := by
    rw [h]
  have h3 : mul (inv (inv a)) (mul (inv a) a) = a := by
    rw [one_mul] at h2
    rw [mul_assoc] at h2
    exact h2
  rw [inv_mul] at h3
  rw [mul_one] at h3
  exact h3

Conclusion "Congrats!"
