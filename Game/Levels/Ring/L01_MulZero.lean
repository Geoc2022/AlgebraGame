import Game.Levels.Group
import Game.MyAlgebra.Ring_Def

World "Ring"
Level 1

Title "Multiplication by Zero"

namespace MyAlgebra

Introduction "
  We now have a ring but how do the additive and multiplicative groups interact? The only axiom we have connecting the two is the distributivity axiom. This turns out to be enough to how the multiplicative group interacts with the additive identity.
"

/--
`mul_zero` is a proof that `a * 0 = 0` for all `a : R` in a ring `R`. This connects the identity element of the additive group with the multiplicative group
-/
TheoremDoc MyAlgebra.mul_zero as "mul_zero" in "Ring"
Statement mul_zero {R} [Ring R] (a : R) : a * 0 = 0 := by
  have h : a * 0 = a * 0 + a * 0 :=
    calc a * 0 = a * (0 + 0) := by rw [add_zero]
      _ = a * 0 + a * 0 := by rw [distrib_left]
  apply add_left_cancel (a * 0)
  rw [← h]
  rw [add_zero]

/--
`zero_mul` is a proof that `0 * a = 0` for all `a : R` in a ring `R`. This connects the identity element of the additive group with the multiplicative group
-/
TheoremDoc MyAlgebra.zero_mul as "zero_mul" in "Ring"
theorem zero_mul {R} [Ring R] (a : R) : 0 * a = 0 := by
  have h : 0 * a = 0 * a + 0 * a :=
    calc 0 * a = (0 + 0) * a := by rw [zero_add]
      _ = 0 * a + 0 * a := by rw [distrib_right]
  apply add_left_cancel (0 * a)
  rw [← h]
  rw [add_zero]


Conclusion "Congrats! You've proved that `a * 0 = 0` for all `a : R` in a ring `R`. This is a very important fact about rings. And the duel of this fact is also true. `0 * a = 0` for all `a : R` in a ring `R`. It turns out this is similar to this proof so we've just added it for you.
"

section Ring_Axioms
/--
`add_zero` is a proof that `0 + r = r` for all `r : R` (Left Additive Identity Axiom).
-/
TheoremDoc add_zero as "add_zero" in "Ring"
/--
`zero_add` is a proof that `r + 0 = r` for all `r : R` (Right Additive Identity Axiom).
-/
TheoremDoc zero_add as "zero_add" in "Ring"

/--
`add_neg` is a proof that `r + (-r) = 0` for all `r : R` (Left Additive Inverse Axiom).
-/
TheoremDoc MyAlgebra.AddGroup.add_neg as "add_neg" in "Ring"
/--
`neg_add` is a proof that `(-r) + r = 0` for all `r : R` (Right Additive Inverse Axiom).
-/
TheoremDoc MyAlgebra.AddGroup.neg_add as "neg_add" in "Ring"

/--
`add_assoc` is a proof that `(r1 + r2) + r3 = r1 + (r2 + r3)` for all `r1, r2, r3 : R` (Additive Associative Law).
-/
TheoremDoc MyAlgebra.AddSemigroup.add_assoc as "add_assoc" in "Ring"

/--
`add_comm` is a proof that `r1 + r2 = r2 + r1` for all `r1, r2 : R` (Additive Commutative Law).
-/
TheoremDoc MyAlgebra.AddCommGroup.add_comm as "add_comm" in "Ring"

/--
`one_mul` is a proof that `1 * r = r` for all `r : R` (Left Multiplicative Identity Axiom).
-/
TheoremDoc one_mul as "one_mul" in "Ring"
/--
`mul_one` is a proof that `r * 1 = r` for all `r : R` (Right Multiplicative Identity Axiom).
-/
TheoremDoc mul_one as "mul_one" in "Ring"

/--
`mul_assoc` is a proof that `(r1 * r2) * r3 = r1 * (r2 * r3)` for all `r1, r2, r3 : R` (Multiplicative Associative Law).
-/
TheoremDoc MyAlgebra.Semigroup.mul_assoc as "mul_assoc" in "Ring"

/--
`distrib_right` is a proof that `(r1 + r2) * r3 = (r1 * r3) + (r2 * r3)` for all `r1, r2, r3 : R` (right Distributive Law).
-/
TheoremDoc MyAlgebra.Ring.distrib_right as "distrib_right" in "Ring"
/--
`distrib_left` is a proof that `r1 * (r2 + r3) = (r1 * r2) + (r1 * r3)` for all `r1, r2, r3 : R` (left Distributive Law).
-/
TheoremDoc MyAlgebra.Ring.distrib_left as "distrib_left" in "Ring"
end Ring_Axioms

section Group_to_Ring_Thm
/--
`add_left` is a proof that if `g1 = g2`, then `h + g1 = h + g2` - basically `h + _` is a function.
-/
TheoremDoc MyAlgebra.add_left as "add_left" in "Ring"

/--
`add_right` is a proof that if `g1 = g2`, then `h * g1 = h * g2` - basically `h * _` is a function.
-/
TheoremDoc MyAlgebra.add_right as "add_left" in "Ring"

/--
`add_left_cancel` is a proof that if `h + g1 = h + g2`, then `g1 = g2` - the inverse of `add_left` is a function.
-/
TheoremDoc MyAlgebra.add_left_cancel as "add_left_cancel" in "Ring"

/--
`add_right_cancel` is a proof that if `g1 + h = g2 + h`, then `g1 = g2` - the inverse of `add_right` is a function.
-/
TheoremDoc MyAlgebra.add_right_cancel as "add_right_cancel" in "Ring"

/--
`neg_neg` is a proof that the negative of an negative is the original element.
-/
TheoremDoc MyAlgebra.neg_neg as "neg_neg" in "Ring"


end Group_to_Ring_Thm


NewTheorem add_zero zero_add MyAlgebra.AddGroup.neg_add MyAlgebra.AddGroup.add_neg MyAlgebra.AddSemigroup.add_assoc MyAlgebra.AddCommGroup.add_comm one_mul mul_one MyAlgebra.Semigroup.mul_assoc MyAlgebra.Ring.distrib_right MyAlgebra.Ring.distrib_left MyAlgebra.zero_mul MyAlgebra.add_left MyAlgebra.add_right MyAlgebra.add_left_cancel MyAlgebra.add_right_cancel MyAlgebra.neg_neg
