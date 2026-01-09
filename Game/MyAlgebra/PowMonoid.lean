import Game.Levels.Monoid

namespace MyAlgebra

/-- The power function for monoids -/
def mpow {M : Type} [Monoid M] (x : M) : ℕ → M
| Nat.zero => 1
| Nat.succ n => (mpow x n) * x

instance {M : Type} [Monoid M] : HPow M ℕ M where
  hPow := mpow

-- Basic lemmas
@[simp]
lemma mpow_eq_hpow (m : M) (n : ℕ) [Monoid M] : mpow m n = m ^ n := rfl

@[simp]
lemma mpow_zero (m : M) [Monoid M] : m ^ 0 = 1 := rfl

/-- m ^ (n + 1) = m ^ n * m -/
@[simp]
lemma mpow_succ_right (m : M) [Monoid M] : m ^ (n+1) = (m ^ n) * m := rfl


-- Start of Monoid Order Levels
/-- m¹ = m -/
@[simp]
lemma mpow_one (m : M) [Monoid M] : m ^ 1 = m := by
  rw [mpow_succ_right, mpow_zero, one_mul]

/-- m ^ (n + 1) = m * m ^ n-/
lemma mpow_succ_left (m : M) [Monoid M] : m ^ (n + 1) = m * (m ^ n) := by
  induction n with
  | zero =>
    rw [mpow_zero, mpow_one]
    rw [mul_one]
  | succ n ih =>
    rw [mpow_succ_right]
    nth_rw 2 [mpow_succ_right]
    rw [ih, mul_assoc]

/--  m ^ (x + y) = m ^ x * m ^ y -/
lemma mpow_add (m : M) (x y : ℕ) [Monoid M]: m ^ (x + y) = (m ^ x) * (m ^ y) := by
  induction y with
  | zero => rw [mpow_zero, mul_one, Nat.add_zero]
  | succ y ih =>
    rw [Nat.add_succ, mpow_succ_right, ih]
    rw [mpow_succ_right]
    rw [mul_assoc]

/-- m ^ (x * y) = (m ^ x) ^ y-/
lemma mpow_mul (m : M) (x y : ℕ) [Monoid M] : m ^ (x * y) = (m ^ x) ^ y := by
  induction y with
  | zero =>
    rw [Nat.mul_zero, mpow_zero, mpow_zero]
  | succ y ih =>
    simp only [mpow_succ_right]
    rw [Nat.mul_succ, mpow_add, ih]

/-- 1 ^ x = 1 -/
@[simp]
lemma mpow_id (x : ℕ) [Monoid M] : 1 ^ x = (1 : M) := by
  induction x with
  | zero => rfl
  | succ x ih => rw [mpow_succ_right, ih, mul_one]

/-- m ^ x * m = m * m ^ x -/
lemma mpow_comm_mul (m: M) (x : ℕ) [Monoid M] : (m ^ x) * m = m * (m ^ x) := by
  induction x with
  | zero => rw [mpow_zero, mul_one, one_mul]
  | succ x ih =>
    nth_rw 1 [mpow_succ_left, mpow_succ_right]
    rw [mul_assoc, ih]
  done

/-- m ^ x * m ^ y = m ^ y * m ^ x -/
lemma mpow_comm_mpow (m : M) (x y : ℕ) [Monoid M] : (m ^ x) * (m ^ y) = (m ^ y) * (m ^ x) := by
  induction y with
  | zero => rw [mpow_zero, mul_one, one_mul]
  | succ y ih =>
    rw [mpow_succ_left]
    rw [mul_assoc]
    rw [← ih]
    rw [← mul_assoc m _ _]
    rw [← mul_assoc _ m _]
    rw [mpow_comm_mul]
