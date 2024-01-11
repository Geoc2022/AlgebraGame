import Game.Levels.GroupHom.L01_HomPreservesOne

World "BasicGroup"
Level 1

Title "Homomorphisms preserve inverses"

namespace MyAlgebra

Introduction ""

/--
`hom_preserves_inv` is a proof that a homomorphism preserves inverses.
-/
TheoremDoc MyAlgebra.hom_preserves_inv as "hom_preserves_inv" in "Group"
@[to_additive]
Statement hom_preserves_inv (f : G → H) [Group G] [Group H] (h : is_mul_hom f) : (f a)⁻¹ = f (a⁻¹) := by
  have q := h a (a⁻¹)
  rw [mul_inv] at q
  rw [hom_preserves_one f h] at q
  apply mul_left_cancel (f a)
  rw [mul_inv]
  rw [←q]

-- theorem hom_preserves_inv' [Group G] [Group H] (f : GroupHom G H) : (f a)⁻¹ = f (a⁻¹) := by
--   have q := f.hom a (a⁻¹)
--   rw [mul_inv] at q
--   rw [hom_preserves_one f] at q
--   apply mul_left_cancel (f a)
--   rw [mul_inv]
--   exact q

Conclusion "Congrats!"
