import Game.Levels.Group
import Game.Levels.PowMonoid
import Game.MyAlgebra.PowGroup

World "Group Power"
Level 1

Title "Negative Natural Exponent"

namespace MyAlgebra

Introduction "We now move to powers with integer exponents.
In this level, you’ll show that `g ^ (-(n : ℤ))` is the inverse of `g ^ n`."

/--
For a group element `g` and a natural number `n`, we have
`g ^ (-(n : ℤ)) = (g ^ n)⁻¹`.
-/
TheoremDoc MyAlgebra.gpow_neg_mpow as "gpow_neg_mpow" in "Group Power"
Statement gpow_neg_mpow {G} [Group G] (g : G) (x : ℕ) :
  g ^ (-(x : ℤ)) = (g ^ x)⁻¹ := by
  Hint "Do a case split on `n` using `cases n with | zero | succ`."
  cases x with
  | zero =>
    rw [Int.ofNat_zero]
    rw [Int.neg_zero]
    rw [gpow_zero g]
    rw [inv_id]
    rfl
  | succ x =>
    have h: -↑(x + 1) = Int.negSucc x := rfl
    rw [h]
    rw [gpow_negSucc]
    simp [inv_mpow, mpow_add, ← inv_anticomm, mpow_one, mpow_comm_mul]

Conclusion "Great! You’ve connected negative integer exponents with inverses of natural powers."
