import Game.Levels.GroupHom.L01_HomPreservesOne

World "BasicGroup"
Level 1

Title "Homomorphisms preserve inverses"

namespace MyAlgebra
-- variable {α : Type} [Group α]

Introduction ""

/--
`hom_preserves_inv` is a proof that a homomorphism preserves inverses.
-/
TheoremDoc MyAlgebra.hom_preserves_inv as "hom_preserves_inv" in "Group"
Statement hom_preserves_inv (f : G → H) [Group G] [Group H] (h : is_hom f) : (f a)⁻¹ = f (a⁻¹) := by
  have q := h a (a⁻¹)
  rw [mul_inv] at q
  rw [hom_preserves_one f h] at q
  apply cancel_left (f a)
  rw [mul_inv]
  rw [←q]

Conclusion "Congrats!"
