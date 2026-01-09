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
