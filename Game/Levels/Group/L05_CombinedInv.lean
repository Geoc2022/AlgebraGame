import Game.Levels.Group.L04_InvUnique

World "Group"
Level 5

Title "Inverse of a Product"

namespace MyAlgebra

Introduction "Our group has inverses of elements by definition but what about the inverse of the product of two elements? Since products of elements are elements of the group, they should have inverses too. This exposes the anti-commutativity of the inverse operation."

/--
`inv_anticomm` is a proof that there exists a inverse of `g * h` in a group.
-/
TheoremDoc MyAlgebra.inv_anticomm as "inv_anticomm" in "Group"
-- @[to_additive]
Statement inv_anticomm (g h : G) [Group G] : (h⁻¹ * g⁻¹) = (g * h)⁻¹ := by
  Hint "You can use `And.intro` to break down the goal into two goals."
  apply inv_unique (g * h) (h⁻¹ * g⁻¹)
  apply And.intro

  rw [← mul_assoc]
  rw [mul_assoc g h _]
  rw [mul_inv]
  rw [mul_one]
  rw [mul_inv]

  rw [← mul_assoc]
  rw [mul_assoc (h⁻¹) (g⁻¹) _]
  rw [inv_mul]
  rw [mul_one]
  rw [inv_mul]


Conclusion "Congrats! Can we say more about the inverse of `g * h`? Maybe using the last level we can answer \"Is it unique?\""
