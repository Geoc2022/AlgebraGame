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

/--
`Nat.add_zero` is a proof that for any natural number `n`, `n + 0 = n`.
-/
TheoremDoc Nat.add_zero as "Nat.add_zero" in "Nat"

/--
`Nat.zero_add` is a proof that for any natural number `n`, `0 + n = n`.
-/
TheoremDoc Nat.zero_add as "Nat.zero_add" in "Nat"

/--
`Nat.add_succ` is a proof that for any natural numbers `n` and `m`, `n + succ m = succ (n + m)`.
-/
TheoremDoc Nat.add_succ as "Nat.add_succ" in "Nat"

/--
`Nat.mul_zero` is a proof that for any natural number `n`, `n * 0 = 0`.
-/
TheoremDoc Nat.mul_zero as "Nat.mul_zero" in "Nat"

/--
`Nat.mul_succ` is a proof that for any natural numbers `n` and `m`, `n * (m + 1) = n * m + n`.
-/
TheoremDoc Nat.mul_succ as "Nat.mul_succ" in "Nat"

NewTheorem Nat.add_zero Nat.zero_add Nat.add_succ Nat.mul_zero Nat.mul_succ MyAlgebra.mpow_one
