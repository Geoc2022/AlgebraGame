import Game.Levels.GroupBasics.L04_CancelRight

World "GroupBasics"
Level 5

Title "Only One One"

namespace MyAlgebra

Introduction "We know from group axioms that there exists an identity element, but is it unique? (Hint: there is only one unique identity) One approach to proving this is to have two \"different\" identities that we see are actually the same.

We will need the following definition:
`def is_one (g : G) [Group G] := ∀ a : G, g * a = a ∧ a * g = a`

This definition is a predicate on `g : α` that says that `g` is an identity element (anything element multiplied by it returns the original element). Remember that we can split up the and (∧) using cases' or by using `And.left` and `And.right`."

/--
`one_unique` is a proof that there is only one identity element in a group
-/
TheoremDoc MyAlgebra.one_unique as "one_unique" in "Group"
@[to_additive]
Statement one_unique (a e1 e2 : G) [Group G] (h1 : is_one e1) (h2 : is_one e2) : e1 = e2 := by
  cases' h1 a with h1l h1r
  cases' h2 a with h2l h2r
  have h := h1r
  rw [←h2r] at h
  rw [mul_assoc] at h
  have q := And.left (h2 e1)
  rw [q] at h
  apply mul_left_cancel a
  exact h

Conclusion "Congrats!"
