import Game.Levels.Group.L01_MulLeft

World "Group"
Level 2

Title "Right Multiplication"

namespace MyAlgebra

Introduction "Here's a duel of that last level."

/--
`mul_right` is a proof that if `g1 = g2`, then `g1 * h = g2 * h` - based on `_ * h` is a well defined function.
-/
TheoremDoc MyAlgebra.mul_right as "mul_left" in "Group"
@[to_additive]
Statement mul_right (g : G) [Group G] : g1 = g2 → g1 * g = g2 * g := by
  intro h
  rw [h]


Conclusion "Don't worry it's going to get a bit more challenging (and a lot more fun)!"
