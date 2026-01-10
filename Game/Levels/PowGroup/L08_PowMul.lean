import Game.Levels.PowGroup.L07_PowSub

World "Group Power"
Level 8

Title "Multiplying Integer Exponents"

namespace MyAlgebra

Introduction "Finally, we prove the multiplication law for integer exponents:
`g ^ (x * y) = (g ^ x) ^ y`."

/--
For any group element `g` and integers `x`, `y`,
we have `g ^ (x * y) = (g ^ x) ^ y`.
-/
TheoremDoc MyAlgebra.gpow_mul as "gpow_mul" in "Group Power"
Statement gpow_mul {G} [Group G] (g : G) (x y : ℤ) :
    g ^ (x * y) = (g ^ x) ^ y := by
  Hint "Use `Int.induction_on` on `y` as in earlier levels."
  induction y using Int.induction_on with
  | zero =>
    Hint "Start with `y = 0`."
    -- x * 0 = 0, and (g^x)^0 = 1
    simp
  | succ n ih =>
    Hint "Use the identity `x * (n+1) = x * n + x` and the addition lemma for powers."
    -- y = n+1
    -- g^(x*(n+1)) = g^(x*n + x) = g^(x*n) * g^x
    -- (g^x)^(n+1) = (g^x)^n * g^x
    rw [mul_add, mul_one, ←gpow_add, gpow_succ, ih]
  | pred n ih =>
    Hint "For the negative step, use `Int.mul_sub` and your subtraction lemma `gpow_sub`."
    -- y = -[n+1]
    -- x * (-(n+1)) = x * (-n) - x
    -- use `gpow_sub` and `gpow_pred` to step down
    rw [Int.mul_sub, mul_one, ←gpow_sub, ←gpow_pred, ih]

Conclusion "Excellent! You’ve proved the full multiplication law for integer exponents."
