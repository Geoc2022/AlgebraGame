import Game.Levels.PowGroup.L02_PowNegOne

World "Group Power"
Level 3

Title "Adding 1 to an Integer Exponent"

namespace MyAlgebra

Introduction "Next, you will show a recursive formula for integer exponents:
`g ^ (n + 1) = g ^ n * g`."

/--
For any group element `g` and integer `x`,
`g ^ (x + 1) = (g ^ x) * g`.
-/
TheoremDoc MyAlgebra.gpow_succ as "gpow_succ" in "Group Power"
Statement gpow_succ {G} [Group G] (g : G) (x : ℤ) :
  g ^ (x + 1) = (g ^ x) * g := by
  Hint "Use `Int.induction_on` on `x`."
  induction x using Int.induction_on with
  | zero =>
    simp
  | succ x ih =>
    Hint "In the nonnegative case, reduce to the natural power `mpow`."
    repeat rw [←Int.ofNat_one]
    repeat rw [Int.ofNat_add_out]
    repeat rw [gpow_ofNat]
    rfl
  | pred x ih =>
    Hint "In the negative case, use `gpow_negSucc`, `mpow_succ_right`, and cancellation."
    rw [←Int.negSucc_coe', gpow_negSucc, mpow_succ_right, mul_assoc, inv_mul, mul_one]
    rw [Int.negSucc_eq, Int.neg_add, Int.neg_add_cancel_right, gpow_neg_mpow]
    exact inv_mpow g x


Conclusion "Good! You now have a recursive rule for integer exponents too."
