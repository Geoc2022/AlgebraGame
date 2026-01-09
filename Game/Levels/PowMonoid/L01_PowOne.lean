import Game.Levels.Monoid
import Game.MyAlgebra.PowMonoid

World "Monoid Power"
Level 1

Title "First Power: m¹ = m"

namespace MyAlgebra

Introduction "We’ve defined the power of an element in a monoid recursively.
In this level you’ll prove the basic fact that `m¹ = m`."

/--
If `m` is an element of a monoid, then `m¹ = m`.
-/
TheoremDoc MyAlgebra.mpow_one as "mpow_one" in "Monoid Power"
Statement mpow_one {M} [Monoid M] (m : M) : m ^ 1 = m := by
  Hint "Recall the definition: `m ^ (n+1) = m ^ n * m` and `m ^ 0 = 1`."
  -- `1` is `0 + 1`, so:
  rw [mpow_succ_right]
  -- Now `m ^ 0 = 1`, so:
  rw [mpow_zero]
  -- and `1 * m = m` by the left identity law:
  rw [one_mul]

Conclusion "Nice! You've taken the first step in using our power function on monoids."
