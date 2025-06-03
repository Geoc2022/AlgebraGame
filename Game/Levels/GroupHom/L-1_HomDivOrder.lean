import Game.Levels.GroupHom.L05_HomCompHom

World "GroupHom"
Level 0

Title "Homomorphisms take elements to elements of order dividing the original element's order."

namespace MyAlgebra

Introduction "

"

/--
`hom_div_order` is a theorem that states that a homomorphism takes elements to elements of order dividing the original element's order.
-/
TheoremDoc MyAlgebra.hom_div_order as "hom_div_order" in "Group"
Statement hom_div_order [Group G] [Group H] (f : GroupHom G H) (a : G) (n : ℕ) : a^n = 1 → (f a)^n = 1 := by
  sorry

-- Conclusion "Congrats!"
