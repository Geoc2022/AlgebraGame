import Game.Levels.Group.L05_OneUnique

World "Group"
Level 6

Title "Unique Inverse"

namespace MyAlgebra

Introduction "Similar to how there's only one identity element, there's only one inverse element. We can use a similar augment from the last level to prove this. If `g1` and `g2` are both inverses of `g`, then `g1 = g2`.

We will need the following definition:
`def is_inv (a b : G) [Group G] := a * b = e ∧ b * a = e`

This definition is a predicate on `a b : α` that says that `b` is an inverse of `a` (multiplying `a` by `b` returns the identity element). Remember that we can split up the and (∧) using cases' or by using `And.left` and `And.right`.
"

/--
  `is_inv g h` says that `g` is an inverse element of `h` (multiplying `g` by `h` returns the identity element)
-/
DefinitionDoc is_inv as "is_inv"
-- @[to_additive]
def is_inv (a b : G) [Group G] := a * b = 1 ∧ b * a = 1
NewDefinition is_inv


/--
`inv_unique` is a proof that there is only one inverse element in a group for any given element.
-/
TheoremDoc MyAlgebra.inv_unique as "inv_unique" in "Group"
-- @[to_additive]
Statement inv_unique (a b c : G) [Group G] (h1 : is_inv a b) (h2 : is_inv a c) : b = c := by
  cases' h1 with h1l h1r
  cases' h2 with h2l h2r
  rw [←h2r] at h1r
  apply mul_right_cancel a
  exact h1r

Conclusion "Congrats!"
