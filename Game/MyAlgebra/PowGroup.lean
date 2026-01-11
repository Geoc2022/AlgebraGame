import Game.Levels.Group
import Game.Levels.PowMonoid

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

@[simp]
lemma gpow_negSucc (g : G) (n : ℕ) [Group G] : g ^ (Int.negSucc n) = (g⁻¹) ^ (n+1) := rfl

@[simp]
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
