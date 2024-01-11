import Game.Levels.GroupBasics.L06_InvUnique

World "GroupBasics"
Level 7

Title "Inverse of a Product"

namespace MyAlgebra

Introduction "Our group has inverses of elements by definition but what about the inverse of the product of two elements? Since products of elements are elements of the group, they should have inverses too. So try and guess what the inverse of `g * h` is. before we prove it."

/--
`inv_prod` is a proof that there exists a inverse of `g * h` in a group.
-/
TheoremDoc MyAlgebra.inv_prod as "inv_prod" in "Group"
@[to_additive]
Statement inv_prod (g h : G) [Group G] : is_inv (h⁻¹ * g⁻¹) (g * h) := by
  apply And.intro

  rw [← mul_assoc]
  rw [mul_assoc (h⁻¹) (g⁻¹) _]
  rw [inv_mul]
  rw [mul_one]
  rw [inv_mul]

  rw [← mul_assoc]
  rw [mul_assoc g h _]
  rw [mul_inv]
  rw [mul_one]
  rw [mul_inv]


Conclusion "Congrats! Can we say more about the inverse of `g * h`? Maybe using the last level we can answer \"Is it unique?\""
