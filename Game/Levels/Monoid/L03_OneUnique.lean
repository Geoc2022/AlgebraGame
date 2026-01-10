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

/--
`obtain ⟨h1, h2⟩ := h` is a tactic that splits `h` into cases and adds them as hypotheses `h1` and `h2`
-/
TacticDoc obtain

/--
`cases' h with h1 h2 ... hn` is a tactic that splits `h` into cases and adds them as hypotheses `h1 h2 ... hn`
-/
TacticDoc cases'

/--
`And.left` and `And.right` are theorems that split an `And` into its left and right components
-/
TheoremDoc And.left as "And.left" in "Basic"
/--
`And.left` and `And.right` are theorems that split an `And` into its left and right components
-/
TheoremDoc And.right as "And.right" in "Basic"

/--
`And.intro` is a theorem that takes two proofs `h1 : P` and `h2 : Q` and returns a proof `h : P ∧ Q`
-/
TheoremDoc And.intro as "And.intro" in "Basic"


NewTactic cases'

NewTheorem And.left And.right And.intro
