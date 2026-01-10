import Game.Levels.PowGroup.L03_PowSucc

World "Group Power"
Level 4

Title "Subtracting 1 from an Integer Exponent"

namespace MyAlgebra

Introduction "Dually to `g^(n+1)`, we can describe `g^(n-1)` by multiplying with `g⁻¹` on the right."

/--
For any group element `g` and integer `x`,
`(g ^ x) * g⁻¹ = g ^ (x - 1)`.
-/
TheoremDoc MyAlgebra.gpow_pred as "gpow_pred" in "Group Power"
Statement gpow_pred {G} [Group G] (g : G) (x : ℤ) :
  (g ^ x) * g⁻¹ = g ^ (x - 1) := by
  Hint "You can proceed by cases on `x` (nonnegative / negative) as in the definition of `gpow`."
  match x with
  | Int.ofNat x =>
    simp only [Int.ofNat_eq_coe]
    cases x with
    | zero =>
      rw [Int.ofNat_zero, gpow_zero]
      rw [one_mul, Int.zero_sub, gpow_neg_one]
    | succ x =>
      simp [Nat.cast_add, Nat.cast_one]
      rw [gpow_succ, mul_assoc, mul_inv, mul_one]
  | Int.negSucc x =>
    rw [Int.negSucc_sub_one, gpow_negSucc, gpow_negSucc]
    repeat rw [mpow_succ_right]

Conclusion "Great! You can move down in the exponent by multiplying on the right with `g⁻¹`."
