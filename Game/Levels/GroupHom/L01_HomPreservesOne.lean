import Game.Levels.GroupBasics.L09_InvInv
import Game.MyAlgebra.Group_Hom_Def

World "GroupHom"
Level 1

Title "Homomorphisms preserve the identity"

namespace MyAlgebra

Introduction "
  After creating groups, it's probably a good idea to define a function between groups. There can be a lot of different functions between groups, but we only care about the ones that preserve the group structure. These functions are called homomorphisms.

  So what makes up the group structure? Well, we have a set `α`, a binary operation `⬝`, and an identity element `e`. Therefore, we need to define a function that preserves these elements.

  It turns out that we only need the binary operation to be preserved. And in the next two levels we get the other two for free.

  We define a homomorphism as a function `f` that satisfies the following property:
  `∀ a b : α, f (a ⬝ b) = f a ⬝ f b`

  And we call this property `is_hom`.
"

/--
`hom_preserves_one` is a proof that a homomorphism preserves the identity element.
-/
TheoremDoc MyAlgebra.hom_preserves_one as "hom_preserves_one" in "Group"
@[to_additive]
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
