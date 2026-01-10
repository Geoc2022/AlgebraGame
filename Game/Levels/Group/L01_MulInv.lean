import Game.Levels.Monoid.L03_OneUnique

World "Group"
Level 1

Title "Right Multiplicative Inverse"

namespace MyAlgebra

Introduction "We will now prove that we the inverse is a also a right multiplicative inverse. This is a bit more challenging than the previous levels, but it will be helpful to know this later on. This is one half of the \"Cancellation Rule for Groups\""

/--
`mul_inv` is a proof that for all `g : G`, `g * g⁻¹ = 1` (Right Inverse Axiom).
-/
TheoremDoc MyAlgebra.mul_inv' as "mul_inv" in "Group"
Statement mul_inv' {G} (g : G) [Group G] : g * g⁻¹ = 1 := by
  Hint "We have a similar lemma for the left inverse, can we use it here?"
  rw [←one_mul (g * _)]
  rw [←inv_mul (g⁻¹)]
  rw [mul_assoc]
  rw [←mul_assoc (g⁻¹)]
  rw [inv_mul]
  rw [one_mul]

Conclusion "Congrats!"

/--
`mul_inv` is a proof that for all `g : G`, `g * g⁻¹ = 1` (Right Inverse Axiom).
-/
TheoremDoc MyAlgebra.Group.mul_inv as "mul_inv" in "Group"

section Group_Axioms
/--
`mul_one` is a proof that for all `g : G`, `1 * g = g` (Left Identity Axiom).
-/
TheoremDoc mul_one as "mul_one" in "Group"
/--
`one_mul` is a proof that for all `g : G`, `g * 1 = g` (Right Identity Axiom).
-/
TheoremDoc one_mul as "one_mul" in "Group"

/--
`inv_mul` is a proof that for all `g : G`, `g⁻¹ * g = 1` (Left Inverse Axiom).
-/
TheoremDoc MyAlgebra.Group.inv_mul as "inv_mul" in "Group"

/--
`mul_assoc` is a proof that for all `g1 g2 g3 : G`, `(g1 * g2) * g3 = g1 * (g2 * g3)` (Associative Law).
-/
TheoremDoc MyAlgebra.Semigroup.mul_assoc as "mul_assoc" in "Group"
end Group_Axioms

NewTheorem MyAlgebra.Group.mul_inv mul_one one_mul MyAlgebra.Group.inv_mul MyAlgebra.Semigroup.mul_assoc
