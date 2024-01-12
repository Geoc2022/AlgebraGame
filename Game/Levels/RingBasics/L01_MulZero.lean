import Game.Levels.GroupHom.L04_HomCompHom
import Game.MyAlgebra.Ring_Def

World "BasicRing"
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
Statement mul_zero {R : Type} [Ring R] (a : R) : a * 0 = 0 := by
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
theorem zero_mul {R : Type} [Ring R] (a : R) : 0 * a = 0 := by
  have h : 0 * a = 0 * a + 0 * a :=
    calc 0 * a = (0 + 0) * a := by rw [zero_add]
      _ = 0 * a + 0 * a := by rw [distrib_right]
  apply add_left_cancel (0 * a)
  rw [← h]
  rw [add_zero]


Conclusion "Congrats! You've proved that `a * 0 = 0` for all `a : R` in a ring `R`. This is a very important fact about rings. And the duel of this fact is also true. `0 * a = 0` for all `a : R` in a ring `R`. It turns out this is similar to this proof so we've just added it for you.
"
