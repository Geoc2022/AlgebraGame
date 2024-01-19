import Game.Levels.Group.L04_CancelRight

World "Group"
Level 5

Title "Only One One"

namespace MyAlgebra

Introduction "We know from group axioms that there exists an identity element, but is it unique? (Hint: there is only one unique identity) One approach to proving this is to have two \"different\" identities that we see are actually the same.

We will need the following definition:
`def is_one (g : G) [Group G] := ∀ a : G, g * a = a ∧ a * g = a`

This definition is a predicate on `g : α` that says that `g` is an identity element (anything element multiplied by it returns the original element). Remember that we can split up the and (∧) using cases' or by using `And.left` and `And.right`."


/--
  `is_one g` says that `g` is an identity element (anything element multiplied by it returns the original element)
-/
DefinitionDoc is_one as "is_one"
-- @[to_additive]
def is_one (g : G) [Group G] := ∀ a : G, g * a = a ∧ a * g = a
NewDefinition is_one

/--
`one_unique` is a proof that there is only one identity element in a group
-/
TheoremDoc MyAlgebra.one_unique as "one_unique" in "Group"
-- @[to_additive]
Statement one_unique (e1 e2 : G) [Group G] (h1 : is_one e1) (h2 : is_one e2) : e1 = e2 := by
  cases' h1 e2 with h1l h1r
  cases' h2 e1 with h2l h2r
  rw [h2r] at h1l
  exact h1l

Conclusion "Congrats!"

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
