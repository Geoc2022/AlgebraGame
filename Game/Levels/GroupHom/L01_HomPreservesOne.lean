import Game.Levels.Group
import Game.MyAlgebra.Group_Hom_Def

World "GroupHom"
Level 1

Title "Homomorphisms preserve the identity"

namespace MyAlgebra

Introduction "
  Here we'll prove that a homomorphism preserves the identity element.

  We define a homomorphism as a function `f` that satisfies the following property:
  `∀ a b : G, f (a * b) = f a * f b`

  And we can access this property by using `f.hom` where `f.hom a b : ∀ a b : G, f (a * b) = f a * f b`.

  We can also use the homomorphism as a function by using `f` directly. Example: `f a`.
"

/--
`hom_preserves_one` is a proof that a homomorphism preserves the identity element.
-/
TheoremDoc MyAlgebra.hom_preserves_one as "hom_preserves_one" in "Group"
-- @[to_additive]
Statement hom_preserves_one [Group G] [Group H] (f : GroupHom G H) : f 1 = 1 := by
  Hint "We probably want to use f.hom with terms that have f 1 to match with the goal"
  Hint "Remmeber that f.hom is a function that takes two arguments"
  have q := f.hom 1 1
  rw [one_mul] at q
  apply mul_right_cancel (f 1)
  rw [one_mul]
  rw [←q]
-- Statement hom_preserves_one [Group G] [Group H] (f : G → H) (h : is_mul_hom f) : f 1 = 1 := by
--   have q := h 1 1
--   rw [one_mul] at q
--   apply mul_right_cancel (f 1)
--   rw [one_mul]
--   rw [←q]


Conclusion "Congrats!"
