import Game.Levels.GroupHom.L03_IdHom

World "GroupHom"
Level 4

Title "The 𝟭 function is a Homomorphism"

namespace MyAlgebra

Introduction "
  Let's check out another example of a homomorphism. Instead of sending elements to themselves let's send them to the trivial group (the group with only the identity). This is called the trivial homomorphism.

  We will denote the trivial homomorphism by oneFunction. It is defined by `oneFunction G H g = 1` for all `g ∈ G`, where the function maps the group `G` to the group `H`.
"

def oneFunction (G H : Type) [Group G] [Group H] : G → H := λ _ => 1

/--
`hom_trival` is a proof that the 𝟭 function is a homomorphism.
-/
TheoremDoc MyAlgebra.hom_trivial as "hom_trivial" in "Group"
Statement hom_trivial {G H : Type} [Group G] [Group H] : ∀ a b : G, oneFunction G H (a * b) = oneFunction G H (a) * oneFunction G H (b)  := by
  intro a b
  rw [oneFunction]
  rw [oneFunction]
  rw [oneFunction]
  rw [mul_one]

Conclusion "Congrats!"
