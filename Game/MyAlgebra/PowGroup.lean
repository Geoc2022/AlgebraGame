import Game.Levels.Group
import Game.MyAlgebra.PowMonoid

namespace MyAlgebra

/-- The power function for groups -/
def gpow {G : Type} [Group G] (x : G) : ℤ → G
| Int.ofNat n => mpow x n
| Int.negSucc n => mpow (x⁻¹) (n+1)

instance {G : Type} [Group G] : HPow G ℤ G where
  hPow := gpow

-- Basic lemmas
@[simp]
lemma gpow_eq_hpow (g : G) (n : ℤ) [Group G] : gpow g n = g ^ n := rfl

@[simp]
lemma gpow_ofNat (g : G) (n : ℕ) [Group G] : g ^ ↑n = g ^ n := rfl

lemma gpow_negSucc (g : G) (n : ℕ) [Group G] : g ^ (Int.negSucc n) = (g⁻¹) ^ (n+1) := rfl

lemma inv_mpow (g : G) (n : ℕ) [Group G] : (g ^ n)⁻¹ = (g⁻¹) ^ n := by
  induction n with
  | zero =>
    simp
    rw [← inv_id]
  | succ n ih =>
    simp
    simp [mpow_add, ← inv_anticomm, ih, mpow_one, mpow_comm_mul]
  done

@[simp]
lemma gpow_zero (g : G) [Group G] : g ^ (0 : ℤ) = 1 := rfl

@[simp]
lemma gpow_one (g : G) [Group G] : g ^ (1 : ℤ) = g := by
  norm_cast
  exact mpow_one g

-- Start of Group Order Levels
lemma gpow_neg_mpow (g : G) (x : ℕ) [Group G] : g ^ (-(x : ℤ)) = (g ^ x)⁻¹ := by
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


@[simp]
lemma gpow_neg_one (g : G) [Group G] : g ^ (-1) = g⁻¹ := by
  rw [←Int.ofNat_one, gpow_neg_mpow]
  simp [mpow_one g]


@[simp]
lemma gpow_succ (g : G) (x : ℤ) [Group G] : g ^ (x + 1) = (g ^ x) * g := by
  induction x using Int.induction_on with
  | hz => rfl
  | hp x _ih =>
    repeat rw [←Int.ofNat_one]
    repeat rw [Int.ofNat_add_out]
    repeat rw [gpow_ofNat]
    rfl
  | hn x _ih =>
    rw [←Int.negSucc_coe', gpow_negSucc, mpow_succ_right, mul_assoc, inv_mul, mul_one]
    rw [Int.negSucc_eq, Int.neg_add, Int.neg_add_cancel_right, gpow_neg_mpow]
    exact inv_mpow g x


lemma gpow_pred (g : G) (x : ℤ) [Group G] : (g ^ x) * (g⁻¹) = g ^ (x - 1) := by
  induction x with
  | ofNat x =>
    simp only [Int.ofNat_eq_coe]
    cases x with
    | zero =>
      rw [Int.ofNat_zero, gpow_zero]
      rw [one_mul, Int.zero_sub, gpow_neg_one]
    | succ x =>
      simp [gpow, Nat.cast_add, Nat.cast_one]
      rw [mul_assoc, mul_inv, mul_one]
  | negSucc x =>
    rw [Int.negSucc_sub_one, gpow_negSucc, gpow_negSucc]
    repeat rw [mpow_succ_right]

lemma gpow_add (g : G) (x y : ℤ) [Group G] : (g ^ x) * (g ^ y) = g ^ (x + y) := by
  induction y using Int.induction_on with
  | hz => rw [add_zero, gpow_zero, mul_one]
  | hp x ihn =>
      simp only [←Int.add_assoc, gpow_succ, mul_assoc]
      rw [←ihn]
      repeat rw [←mul_assoc]
  | hn x ihn =>
    rw [←gpow_pred, ←mul_assoc, ihn, gpow_pred, Int.add_sub_assoc]

lemma gpow_neg (g : G) (x : ℤ) [Group G] : g ^ (-x) = (g ^ x)⁻¹ := by
  induction x using Int.induction_on with
  | hz => rw [neg_zero, gpow_zero, ←inv_id]
  | hp x ih =>
    rw [Int.neg_add, ←Int.sub_eq_add_neg, ←gpow_pred, ih, inv_anticomm, ←Int.add_comm]
    rw [←gpow_add]
    rw [gpow_one]
  | hn x ih =>
    simp at *
    rw [Int.add_comm, gpow_succ, ih, ←gpow_pred, gpow_neg_mpow, inv_anticomm]
    repeat rw [← inv_inv]
    rw [← mpow_succ_right, mpow_succ_left]

@[simp]
lemma gpow_sub (g : G) (x y : ℤ) [Group G] : (g ^ x) * ((g ^ y)⁻¹) = g ^ (x - y) := by
  rw [sub_eq_add_neg, ←gpow_add, gpow_neg]


lemma gpow_mul (g : G) (x y : ℤ) [Group G] : g ^ (x * y) = (g ^ x) ^ y := by
  induction y using Int.induction_on with
  | hz => rw [mul_zero, gpow_zero, gpow_zero]
  | hp n ih => rw [mul_add, mul_one, ←gpow_add, gpow_succ, ih]
  | hn n ih => rw [Int.mul_sub, mul_one, ←gpow_sub, ←gpow_pred, ih]

-- theorem gpow_closure {H : Subgroup G} {n : ℤ}: x ∈ H → gpow x n ∈ H := by
--   intro h
--   induction n using Int.induction_on with
--   | hz => exact H.one_mem
--   | hp n ih =>
--     rw [gpow_succ]
--     apply H.mul_closure
--     · exact ih
--     · exact h
--   | hn n ih =>
--     rw [←gpow_pred, gpow_neg]
--     apply H.mul_closure
--     · rw [←gpow_neg]
--       exact ih
--     · apply H.inv_closure
--       exact h
