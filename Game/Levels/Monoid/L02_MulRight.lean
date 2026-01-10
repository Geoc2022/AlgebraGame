import Game.Levels.Monoid.L01_MulLeft

World "Monoid"
Level 2

Title "Right Multiplication"

namespace MyAlgebra

Introduction "Here's a dual of that last level."

/--
`mul_right` is a proof that if `m1 = m2`, then `m1 * m = m2 * m` - based on `_ * m` is a well defined function.
-/
TheoremDoc MyAlgebra.mul_right as "mul_right" in "Monoid"
@[to_additive]
Statement mul_right {M} (m : M) {m1 m2 : M} [Monoid M] : m1 = m2 → m1 * m = m2 * m := by
  intro h
  rw [h]


Conclusion "Don't worry it's going to get a bit more challenging (and a lot more fun)!"
