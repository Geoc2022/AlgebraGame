import Game.Levels.Group.L09_CombinedInv2

World "Group"
Level 10

Title "Inverse of the Identity"

namespace MyAlgebra

Introduction "In this section, we will prove that the inverse of the identity element is the identity element itself."

/--
`inv_id` is a proof that the inverse of the identity is the identity.
-/
TheoremDoc MyAlgebra.inv_id as "inv_id" in "Group"
-- @[to_additive]
Statement inv_id [Group G] : (1 : G) = (1 : G)⁻¹ := by
  apply inv_unique 1

  constructor
  rw [mul_one]
  rw [one_mul]


Conclusion "Congrats!"
