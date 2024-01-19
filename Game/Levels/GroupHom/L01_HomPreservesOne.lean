import Game.Levels.Group
import Game.MyAlgebra.Group_Hom_Def

World "GroupHom"
Level 1

Title "Homomorphisms preserve the identity"

namespace MyAlgebra

Introduction "
  Here we'll prove that a homomorphism preserves the identity element.

  We define a homomorphism as a function `f` that satisfies the following property:
  `∀ a b : α, f (a * b) = f a * f b`

  And we call this property `is_mul_hom`.
"

/--
`is_mul_hom` is a proof that a function preserves multiplication.
-/
TheoremDoc MyAlgebra.is_mul_hom as "is_mul_hom" in "Group"
-- @[to_additive]
def is_mul_hom {G H : Type} [Group G] [Group H] (f : G → H)  := ∀ a b : G, f (a * b) = (f a) * (f b)
NewDefinition is_mul_hom

/--
`hom_preserves_one` is a proof that a homomorphism preserves the identity element.
-/
TheoremDoc MyAlgebra.hom_preserves_one as "hom_preserves_one" in "Group"
-- @[to_additive]
Statement hom_preserves_one [Group G] [Group H] (f : G → H) (h : is_mul_hom f) : f 1 = 1 := by
  have q := h 1 1
  rw [one_mul] at q
  apply mul_right_cancel (f 1)
  rw [one_mul]
  rw [←q]

-- theorem hom_preserves_one [Group G] [Group H] (f : GroupHom G H) : f 1 = 1 := by
--   have q := f.hom 1 1
--   rw [one_mul] at q
--   apply mul_right_cancel (f 1)
--   rw [one_mul]
--   rw [←q]

Conclusion "Congrats!"
