import Game.Levels.GroupHom.L03_IdHom

World "BasicGroup"
Level 4

Title "Composition of homomorphism is also a homomorphism"

namespace MyAlgebra

Introduction "
  We have seen that the identity function is a homomorphism. Now we will see that the composition of two homomorphisms is also a homomorphism.
"

/--
`hom_comp_hom` is a proof that composition of homomorphisms is also a homomorphism.
-/
TheoremDoc MyAlgebra.hom_comp_hom as "hom_comp_hom" in "Group"
Statement hom_comp_hom (f1 : G → H) (f2 : H → J) [Group G] [Group H] [Group J] (h1 : is_mul_hom f1) (h2 : is_mul_hom f2) : is_mul_hom (f2 ∘ f1) := by
  intro a b
  have q := h1 a b
  have r := h2 (f1 a) (f1 b)
  rw [← q] at r
  exact r

-- theorem hom_comp_hom [Group G] [Group H] [Group J] (f1 : GroupHom G H) (f2 : GroupHom H J) : GroupHom G J := by
--   use f2 ∘ f1
--   intro a b
--   have h1 := f1.hom a b
--   have h2 := f2.hom (f1 a) (f1 b)
--   rw [← h1] at h2
--   exact h2

Conclusion "Congrats!"
