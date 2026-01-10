import Game.Levels.PowGroup.L05_PowAdd

World "Group Power"
Level 6

Title "Negating the Exponent"

namespace MyAlgebra

Introduction "You’ve seen that negative naturals correspond to inverses.
Now you’ll prove the full statement: `g ^ (-n) = (g ^ n)⁻¹` for any integer `n`."

/--
For any group element `g` and integer `n`,
`g ^ (-n) = (g ^ n)⁻¹`.
-/
TheoremDoc MyAlgebra.gpow_neg as "gpow_neg" in "Group Power"
Statement gpow_neg {G} [Group G] (g : G) (n : ℤ) :
  g ^ (-n) = (g ^ n)⁻¹ := by
  Hint "Use `Int.induction_on` on `n`."
  induction n using Int.induction_on with
  | zero =>
    -- n = 0
    simp [gpow_zero, ←inv_id]
  | succ n ih =>
    Hint "Relate `-(n+1)` to `-n - 1` and use `gpow_pred`."
    rw [Int.neg_add, ←Int.sub_eq_add_neg, ←gpow_pred, ih, inv_anticomm, ←Int.add_comm]
    rw [←gpow_add]
    rw [gpow_one]
  | pred n ih =>
    Hint "Use the case for a natural number via `gpow_neg_mpow` and your previous lemma."
    simp at *
    rw [Int.add_comm, gpow_succ, ih, ←gpow_pred, gpow_neg_mpow, inv_anticomm]
    repeat rw [← inv_inv]
    rw [← mpow_succ_right, mpow_succ_left]

Conclusion "Nice! You’ve fully connected negative integer exponents with group inverses."
