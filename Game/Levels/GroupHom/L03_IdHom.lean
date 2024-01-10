import Game.Levels.GroupHom.L02_HomPreservesInv

World "BasicGroup"
Level 3

Title "The Identity Function is a Homomorphism"

namespace MyAlgebra
-- variable {α : Type} [Group α]

Introduction "
  Let's check out an example of a homomorphism. Here's a simple one: the identity function.
"

/--
`hom_id` is a proof that the identity function from a group to itself is a homomorphism.
-/
TheoremDoc MyAlgebra.hom_id as "hom_id" in "Group"
Statement hom_id [Group G] : is_hom (id : G → G) := by
  intro a b
  rfl

Conclusion "Congrats!"
