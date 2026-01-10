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
    simp [inv_mpow, ← inv_anticomm, mpow_comm_mul]

Conclusion "Great! You’ve connected negative integer exponents with inverses of natural powers."

section Group_Power_Axioms
/--
`MyAlgebra.gpow_one` is a proof that for a group element `g`, `g ^ 1 = g`.
-/
TheoremDoc MyAlgebra.gpow_one as "gpow_one" in "Group Power"

/--
`MyAlgebra.gpow_zero` is a proof that for a group element `g`, `g ^ 0 = 1`.
-/
TheoremDoc MyAlgebra.gpow_zero as "gpow_zero" in "Group Power"

/--
`MyAlgebra.gpow_negSucc` is a proof that `g ^ (- (n + 1)) = (g ^ (n + 1))⁻¹`.
-/
TheoremDoc MyAlgebra.gpow_negSucc as "gpow_negSucc" in "Group Power"

/--
`MyAlgebra.gpow_ofNat` is a proof that `g ^ (n : ℤ) = g ^ n` (natural power).
-/
TheoremDoc MyAlgebra.gpow_ofNat as "gpow_ofNat" in "Group Power"

/--
`MyAlgebra.Group.inv_mul` is a proof that for all `g : G`, `g⁻¹ * g = 1` (Left Inverse Axiom).
-/
TheoremDoc MyAlgebra.Group.inv_mul as "inv_mul" in "Group Power"

/--
`MyAlgebra.inv_mpow` is a proof that `(a^n)⁻¹ = a^(-n)`.
-/
TheoremDoc MyAlgebra.inv_mpow as "inv_mpow" in "Group Power"
end Group_Power_Axioms

/--
`Nat.cast_one` is a proof that `(1 : ℤ) = 1`.
-/
TheoremDoc Nat.cast_one as "Nat.cast_one" in "Nat"

/--
`Int.neg_zero` is a proof that `-0 = 0`.
-/
TheoremDoc Int.neg_zero as "Int.neg_zero" in "Int"

/--
`sub_eq_add_neg` is a proof that `x - y = x + (-y)`.
-/
TheoremDoc sub_eq_add_neg as "sub_eq_add_neg" in "Group Power"

/--
`Int.ofNat_zero` is a proof that `(0 : ℤ) = 0`.
-/
TheoremDoc Int.ofNat_zero as "Int.ofNat_zero" in "Int"

/--
`Int.sub_eq_add_neg` is a proof that `x - y = x + (-y)` for integers.
-/
TheoremDoc Int.sub_eq_add_neg as "Int.sub_eq_add_neg" in "Int"

/--
`Int.mul_add` is a proof that `a * (b + c) = a * b + a * c`.
-/
TheoremDoc Int.mul_add as "Int.mul_add" in "Int"

/--
`Int.mul_one` is a proof that `a * 1 = a`.
-/
TheoremDoc Int.mul_one as "Int.mul_one" in "Int"

/--
`Int.zero_sub` is a proof that `0 - n = -n`.
-/
TheoremDoc Int.zero_sub as "Int.zero_sub" in "Int"

/--
`Int.add_sub_assoc` is a proof that `a + (b - c) = (a + b) - c`.
-/
TheoremDoc Int.add_sub_assoc as "Int.add_sub_assoc" in "Int"

/--
`Int.negSucc_coe'` is a proof that `- (n + 1) = Int.negSucc n`.
-/
TheoremDoc Int.negSucc_coe' as "Int.negSucc_coe'" in "Int"

/--
`Int.negSucc_eq` is a proof that `- (n + 1) = Int.negSucc n`.
-/
TheoremDoc Int.negSucc_eq as "Int.negSucc_eq" in "Int"

/--
`Int.neg_add_cancel_right` is a proof that `(-a + b) + a = b`.
-/
TheoremDoc Int.neg_add_cancel_right as "Int.neg_add_cancel_right" in "Int"

/--
`Int.negSucc_sub_one` is a proof that `Int.negSucc n - 1 = Int.negSucc (n + 1)`.
-/
TheoremDoc Int.negSucc_sub_one as "Int.negSucc_sub_one" in "Int"

/--
`Int.ofNat_add_out` is a proof that `↑(m + n) = ↑m + ↑n`.
-/
TheoremDoc Int.ofNat_add_out as "Int.ofNat_add_out" in "Int"

/--
`Int.ofNat_one` is a proof that `(1 : ℤ) = 1`.
-/
TheoremDoc Int.ofNat_one as "Int.ofNat_one" in "Int"

/--
`Int.add_assoc` is a proof that `(a + b) + c = a + (b + c)`.
-/
TheoremDoc Int.add_assoc as "Int.add_assoc" in "Int"

/--
`Nat.cast_add` is a proof that `↑(a + b) = ↑a + ↑b`.
-/
TheoremDoc Nat.cast_add as "Nat.cast_add" in "Nat"

/--
`Int.neg_add` is a proof that `- (a + b) = -a + -b`.
-/
TheoremDoc Int.neg_add as "Int.neg_add" in "Int"

/--
`Int.add_comm` is a proof that `a + b = b + a`.
-/
TheoremDoc Int.add_comm as "Int.add_comm" in "Int"

/--
`Int.ofNat_eq_coe` is a proof that `(n : ℤ) = ↑n`.
-/
TheoremDoc Int.ofNat_eq_coe as "Int.ofNat_eq_coe" in "Int"

/--
`Int.mul_sub` is a proof that `a * (b - c) = a * b - a * c`.
-/
TheoremDoc Int.mul_sub as "Int.mul_sub" in "Int"

NewTheorem Nat.cast_one Int.neg_zero MyAlgebra.gpow_one sub_eq_add_neg MyAlgebra.gpow_zero Int.ofNat_zero Int.sub_eq_add_neg MyAlgebra.gpow_negSucc Int.mul_add Int.mul_one MyAlgebra.gpow_ofNat Int.zero_sub Int.add_sub_assoc Int.negSucc_coe' MyAlgebra.inv_mpow Int.negSucc_eq Int.neg_add_cancel_right Int.negSucc_sub_one Int.ofNat_add_out Int.ofNat_one Int.add_assoc Nat.cast_add Int.neg_add Int.add_comm Int.ofNat_eq_coe Int.mul_sub MyAlgebra.gpow_neg_mpow

/--
`Int.ofNat n` casts a natural number `n` to an integer.
-/
DefinitionDoc Int.ofNat as "Int.ofNat" in "Int"

/--
`Int.negSucc n` represents the integer `-(n + 1)`.
-/
DefinitionDoc Int.negSucc as "Int.negSucc" in "Int"

/--
`MyAlgebra.gpow g n` is the integer power of a group element `g` to the power `n`.
-/
DefinitionDoc MyAlgebra.gpow as "gpow" in "Group Power"

NewDefinition Int.ofNat Int.negSucc MyAlgebra.gpow

/--
The `Int.induction_on` tactic performs induction on an integer `z`.
-/
TacticDoc Int.induction_on

/--
The `match` tactic performs pattern matching on an expression.
-/
TacticDoc «match»

/--
The `cases` tactic performs case analysis on an inductive type.
-/
TacticDoc «cases»

NewTactic Int.induction_on «match» «cases»
