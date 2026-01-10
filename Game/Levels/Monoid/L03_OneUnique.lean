import Game.Levels.Monoid.L02_MulRight

World "Monoid"
Level 3

Title "Only One One"

namespace MyAlgebra

Introduction "We know from monoid axioms that there exists an identity element, but is it unique? One approach to proving this is to have two \"different\" identities that we see are actually the same."

/--
`id_unique` is a proof that there is only one identity element in a monoid
-/
TheoremDoc MyAlgebra.id_unique as "id_unique" in "Monoid"
-- @[to_additive]
Statement id_unique {M} (w : M) [Monoid M] (h : ∀ (m : M), (m * w = m ∧ w * m = m)) : w = 1 := by
  obtain ⟨h1, h2⟩ := h 1
  rw [mul_one] at h2
  rw [one_mul] at h1
  exact h1


Conclusion "Congrats!"
