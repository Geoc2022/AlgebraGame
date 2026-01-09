import Mathlib.Data.Nat.Basic
import Game.Levels.PowGroup

namespace MyAlgebra

def isFiniteOrder {M : Type} [Monoid M] (x : M): Prop := ∃ (n : ℕ), n ≠ 0 ∧ x ^ n = 1

noncomputable def order {M : Type} [Monoid M] (x : M) : ℕ := by
  classical exact if h : isFiniteOrder x then Nat.find h else 0

/-- If m^x = 1 → n = 0 -/
lemma mpow_order_zero (m : M) [Monoid M] (h0 : order m = 0) : m ^ x = 1 → x = 0 := by
  intro hn
  dsimp [order] at h0
  split_ifs at h0 with h
  · absurd h0
    classical have hFinite : ¬(Nat.find h) = 0 ∧ m ^ (Nat.find h) = 1 := Nat.find_spec h
    exact hFinite.left
  · contrapose! h
    use x

/-- If x is the order of m, then m^x = 1 -/
lemma mpow_order (m : M) [Monoid M] : m ^ (order m) = 1 := by
  set n := order m with hn
  rw [order] at hn
  split_ifs at hn with h <;> rw [hn]
  · classical exact (Nat.find_spec h).right
  · rfl


/-- Let x be the order of m. Write x = nq + r with 0 ≤ r < x. Then, m^r = m^x  -/
lemma mpow_mod_order (m : M) (x : ℕ) [Monoid M] : m ^ (x % order m) = m ^ x := by
  set n := order m
  nth_rw 2 [←Nat.mod_add_div x n]
  rw [mpow_add, mpow_mul, mpow_order, mpow_id, mul_one]
  done

/-- Let n be the order of m. m^x = 1 ↔ n | x -/
lemma order_divides_iff_mpow_id (m : M) [Monoid M] : m ^ x = 1 ↔ order m ∣ x := by
  apply Iff.intro
  · intro hm
    by_cases hm0 : x = 0
    · use 0
      rw [mul_zero, hm0]
    · set n := order m with hn
      rw [order] at hn
      split_ifs at hn with h
      · by_contra hnm
        have : x % n < n
        · apply Nat.mod_lt
          rw [hn, GT.gt, pos_iff_ne_zero]
          classical exact (Nat.find_spec h).left
        · nth_rw 2 [hn] at this
          classical apply Nat.find_min h this
          apply And.intro
          · rw [ne_eq, ←Nat.dvd_iff_mod_eq_zero n x]
            exact hnm
          · rw [mpow_mod_order, hm]
      · exfalso
        apply h
        use x
  · rintro ⟨k, rfl⟩
    rw [mpow_mul, mpow_order, mpow_id]
  done


/-- The order of m is nonzero if and only if there exists an n : ℕ such that mⁿ = e -/
lemma order_nonzero_iff (m : M) [Monoid M] : order m ≠ 0 ↔ ∃ n ≠ 0, m ^ n = 1 := by
  apply Iff.intro
  · intro h
    use order m
    apply And.intro h
    exact mpow_order m
  · intro ⟨n, hn⟩
    by_contra! c0
    absurd hn.left
    apply mpow_order_zero m c0
    exact hn.right


/-- The order of the identity element, 1, in any monoid is 1. -/
lemma order_id [Monoid M] : order (1 : M) = 1 := by
  unfold order
  split
  · case _ h =>
    unfold isFiniteOrder at h
    classical rw [Nat.find_eq_iff]
    apply And.intro
    · apply And.intro
      · exact Nat.one_ne_zero
      · exact mpow_id 1
    · intro n hn
      rw [and_iff_not_or_not, not_not]
      left
      push_neg
      exact Nat.lt_one_iff.mp hn
  · case _ h =>
    absurd h
    use 1
    apply And.intro
    · exact Nat.one_ne_zero
    · exact mpow_id 1

/-- Let x be the order of m and let n : ℕ with n ≠ 0. If m ≠ 0, then the order of mⁿ is nonzero -/
lemma mpow_nonzero_order (m : M) [Monoid M] (n : ℕ) (h : order m ≠ 0) : order (m ^ n) ≠ 0 := by
  obtain ⟨x, hm⟩ := (order_nonzero_iff m).mp h
  suffices : ∃ k ≠ 0, (m ^ n) ^ k = 1
  · rw [order_nonzero_iff]
    exact this
  use x
  apply And.intro
  · exact hm.left
  · rw [←mpow_mul, Nat.mul_comm, mpow_mul, hm.right, mpow_id]

/-
In any monoid, if the order of m is nonzero, then there is an element n that serves as both a left
and right inverse to m.
-/
lemma inverse_of_nonzero_order (m : M) [Monoid M] (h : order m ≠ 0) : ∃ (n : M), m * n = 1 ∧ n * m = 1 := by
  use m ^ (order m - 1)
  apply And.intro
  · nth_rw 1 [←mpow_one m]
    rw [←mpow_add, Nat.add_comm]
    rw [Nat.sub_add_cancel]
    · exact mpow_order m
    · exact Nat.one_le_iff_ne_zero.mpr h
  · nth_rw 3 [←mpow_one m]
    rw [←mpow_add]
    rw [Nat.sub_add_cancel]
    · exact mpow_order m
    · exact Nat.one_le_iff_ne_zero.mpr h

/-- Suppose x, y < `order m`. If m^x = m^y, then x = y -/
lemma mpow_inj_of_lt_order (m : M) [Monoid M] (x y : ℕ) (hx : x < order m) (hy : y < order m)
  (h : m ^ x = m ^ y) : x = y := by
  wlog hxy : x ≤ y
  · symm
    exact this m y x hy hx (Eq.symm h) (Nat.le_of_not_ge hxy)
  obtain ⟨k, hk⟩ := Nat.le.dest hxy
  suffices : k = 0
  · rw [this, add_zero] at hk
    exact hk
  apply Nat.eq_zero_of_dvd_of_lt
  · rw [←order_divides_iff_mpow_id m]
    have op_cancel_left : ∀ u v : M, (m ^ x) * u = (m ^ x) * v → u = v
    · intro u v heq
      rw [←one_mul u, ←one_mul v]
      have : ∃ (m' : M), m' * (m ^ x) = 1
      · have : order m ≠ 0 := by linarith
        by_cases hm' : x = 0
        · use 1
          rw [one_mul, hm', mpow_zero]
        · have this := mpow_nonzero_order m x this
          obtain ⟨m', hx'⟩ := inverse_of_nonzero_order (m ^ x) this
          use m'
          exact hx'.right
      obtain ⟨m', op_inv⟩ := this
      repeat rw [←op_inv]
      repeat rw [mul_assoc]
      rw [heq]
    apply op_cancel_left
    rw [mul_one, ←mpow_add, hk]
    exact Eq.symm h
  · rw [←hk] at hy
    linarith

/-- Let r ≠ 0 be the order of m. If m^x = m^y, then y is congruent to x (mod r) -/
lemma mod_order_eq_of_mpow_eq (m : M) [Monoid M] (h : order m ≠ 0) (x y : ℕ)
  : m ^ x = m ^ y → x % (order m) = y % (order m) := by
  intro heq
  apply mpow_inj_of_lt_order m (x % order m) (y % order m)
  · apply Nat.mod_lt
    exact Nat.zero_lt_of_ne_zero h
  · apply Nat.mod_lt
    exact Nat.zero_lt_of_ne_zero h
  · repeat rw [mpow_mod_order]
    exact heq
  done


/-- Let x be the order g. Then, g^x = 1 -/
lemma gpow_order (g : G) [Group G] : g ^ (order g) = 1 := by
  rw [gpow_ofNat, mpow_order]

/- For any integer x, 1^x = 1, if 1 is the identity of a group G. -/
lemma gpow_id (x : ℤ) [Group G] : (1 : G) ^ x = 1 := by
  cases x with
  | ofNat x =>
    rw [Int.ofNat_eq_coe]
    exact mpow_id x
  | negSucc x =>
    rw [gpow_negSucc, mpow_succ_right, ← inv_id, mul_one, mpow_id]

/-- Suppose the order of g is 0. Then if g^x = 1, x = 0 -/
lemma gpow_order_zero (g : G) [Group G] {x : ℤ} (h0 : order g = 0) : g ^ x = 1 → x = 0 := by
  intro h
  cases x with
  | ofNat x =>
    -- Directly go to the `mpow_order_zero` case for natural numbers
    congr
    exact mpow_order_zero g h0 h
  | negSucc x =>
    -- Handle negative case
    exfalso
    absurd h0
    push_neg
    rw [order_nonzero_iff]
    use x + 1
    apply And.intro
    · exact Nat.succ_ne_zero x
    · have q := inv_inj (g^(x + 1)) 1
      rw [← q]
      rw [← inv_id, inv_mpow]
      exact h

/-- Let x be the order g. Write x = q * n + r with 0 ≤ r < x. Then, g^r = g^n -/
lemma gpow_mod_order (g : G) [Group G] {x : ℤ} : g ^ (x % order g) = g ^ x := by
  -- Deal with the integer cases
  cases x with
  | ofNat x =>
    have : (x : ℤ) % (↑(order g)) = (x % order g : ℕ) := rfl
    rw [Int.ofNat_eq_coe]
    rw [this]
    have q := mpow_mod_order g x
    simp at q
    exact q
  | negSucc x =>
    nth_rw 2 [←Int.emod_add_ediv (Int.negSucc x) (order g)]
    rw [←gpow_add, gpow_mul]
    -- rw [gpow_order, gpow_id, mul_one]
    sorry

/-- Suppose the order of g is 0. Then g^x = g^y → x = y -/
lemma gpow_inj_of_order_zero (g : G) [Group G] {x y : ℤ} (h : order g = 0) (heq : g ^ x = g ^ y) : x = y := by
  induction y using Int.induction_on generalizing x with
  | hz =>
    apply gpow_order_zero g h
    exact heq
  | hp y ih =>
    rw [←Int.sub_add_cancel x 1]
    congr 1
    apply ih
    rw [←gpow_pred, heq, gpow_succ, mul_assoc, mul_inv, mul_one]
  | hn y ih =>
    rw [←Int.add_sub_cancel x 1]
    congr 1
    apply ih
    rw [gpow_succ, heq, ←gpow_pred, mul_assoc, inv_mul, mul_one]

/-
This lemma has nothing to do with `order`, but it is essential to the following theorem.
If `x` is a positive integer, then every integer is congruent [MOD x] to some natural number.
-/
lemma emod_has_nat {y : ℕ} (x : ℤ) (hy : 0 < y) : ∃ (z : ℕ), x % y = z % y := by
  -- cases x with
  -- | ofNat x =>
  --   use x
  --   rfl
  -- | negSucc x =>
  --   use y - 1 - x % y

  --   rw [Int.natCast_sub, Int.natCast_sub]
  --   · rw [Int.ofNat_emod x y, Nat.cast_one]
  --     rw [←@Int.negSucc_emod x y]
  --     symm
  --     apply Int.emod_emod
  --     rw [Int.ofNat_pos]
  --     exact hy
  --   · exact hy
  --   · apply Nat.le_sub_one_of_lt
  --     apply Nat.mod_lt
  --     exact hy
  sorry

/--
The capstone theorem of `gpow`: let r = order g. Then if two integers `x` and `y` satisfy g^x = g^y,
then x ≡ y [MOD order g]. If r = 0, then x = y.
-/
lemma mod_order_eq_of_gpow_eq (g : G) [Group G] {x y : ℤ}
  : g ^ x = g ^ y → x % (order g) = y % (order g) := by
  intro h
  by_cases h₀ : order g = 0
  · rw [h₀]
    simp
    exact gpow_inj_of_order_zero g h₀ h
  · obtain ⟨x', hx'⟩ := emod_has_nat x (Nat.zero_lt_of_ne_zero h₀)
    obtain ⟨y', hy'⟩ := emod_has_nat y (Nat.zero_lt_of_ne_zero h₀)
    rw [hx', hy']
    repeat rw [←Int.ofNat_emod]
    congr 1
    have q := mod_order_eq_of_mpow_eq g h₀ x' y'
    rw [q]
    rw [←mpow_mod_order g x', ←mpow_mod_order g y']
    rw [← Int.ofNat_emod] at hx' hy'
    -- have : g ^ x' = g ^ y' :=
    sorry
    -- rw [←hx', ←hy']
    -- repeat rw [gpow_mod_order]
    -- exact h
