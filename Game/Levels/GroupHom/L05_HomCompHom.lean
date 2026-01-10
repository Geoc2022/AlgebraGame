import Game.Levels.GroupHom.L04_OneHom

World "GroupHom"
Level 5

Title "Composition of homomorphism is also a homomorphism"

namespace MyAlgebra

Introduction "
  We have seen that the identity function is a homomorphism. Now we will see that the composition of two homomorphisms is also a homomorphism.

  `GroupHom` is defined as a structure with a proof that the function is a homomorphism, and the function itself. To create a new `GroupHom` instance, we need to provide the function and the proof.

  We can use the `use` tactic to prove the existence of a type using construction. For example to prove that there is a number `x ∈ ℤ` such that `∀ n : ℤ, x + n = n` you can write `use 0` which will replace the goal with `0 + n = n`. In this case, you might want to use it to create a new `GroupHom` instance. The tactic `use` takes a function as an argument, and then asks us to prove that the function is a homomorphism.

  Furthermore, you can construct functions using `λ` notation and ∘ (written \"\\circ\"). For example, `λ x y, x + y` is the function that takes `x, y` to `x + y`. And `f ∘ g` is the function that takes `x` to `f (g x)`.
"

/--
`hom_comp_hom` is a proof that composition of homomorphisms is also a homomorphism.
-/
TheoremDoc MyAlgebra.hom_comp_hom as "hom_comp_hom" in "Group"
Statement hom_comp_hom {G H J} [Group G] [Group H] [Group J] (f1 : GroupHom G H) (f2 : GroupHom H J) : GroupHom G J := by
  Hint "Use the `use` tactic with the form `use f` where `f` is the function you want to use."
  Hint "Use `λ` notation and/or `∘` (written \"\\circ\") to construct functions"
  use f2 ∘ f1
  intro a b
  have h1 := f1.hom a b
  have h2 := f2.hom (f1 a) (f1 b)
  rw [← h1] at h2
  exact h2
-- Statement hom_comp_hom (f1 : G → H) (f2 : H → J) [Group G] [Group H] [Group J] (h1 : is_mul_hom f1) (h2 : is_mul_hom f2) : is_mul_hom (f2 ∘ f1) := by
--   intro a b
--   have q := h1 a b
--   have r := h2 (f1 a) (f1 b)
--   rw [← q] at r
--   exact r

/--
`use h` is a tactic used to provide a proof of a type using construction.
-/
TacticDoc use

NewTactic use

Conclusion "Congrats!"
