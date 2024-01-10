import Mathlib.Tactic.Cases

namespace MyGroup

class Group (α : Type) where
  mul           : α → α → α

  one           : α
  one_mul       : ∀a, mul one a = a
  mul_one       : ∀a, mul a one = a

  inv           : α → α
  mul_left_inv  : ∀a, mul (inv a) a = one
  mul_right_inv : ∀a, mul a (inv a) = one

  mul_assoc     : ∀a b c, mul (mul a b) c = mul a (mul b c)

-- infixr:45 " * " => Group.mul


variable {α : Type} [Group α]

open Group

theorem qwerty (a : α) : mul (inv a) a = one := by
  rw [mul_left_inv]

def is_one (e : α) := ∀ a : α, mul e a = a ∧ mul a e = a

theorem mul_right (h : α) : g1 = g2 → mul g1 h = mul g2 h := by
  intro h1
  rw [h1]

theorem mul_left (h : α) : g1 = g2 → mul h g1 = mul h g2 := by
  intro h1
  rw [h1]

theorem cancel_right (h : α) : mul g1 h = mul g2 h → g1 = g2 := by
  intro h1
  have q := mul_right (inv h) h1
  rw [mul_assoc] at q
  rw [mul_right_inv] at q
  rw [mul_assoc] at q
  rw [mul_right_inv] at q
  rw [mul_one] at q
  rw [mul_one] at q
  exact q

theorem cancel_left (h : α) : mul h g1 = mul h g2 → g1 = g2 := by
  intro h1
  have q := mul_left (inv h) h1
  rw [←mul_assoc] at q
  rw [mul_left_inv] at q
  rw [←mul_assoc] at q
  rw [mul_left_inv] at q
  rw [one_mul] at q
  rw [one_mul] at q
  exact q


theorem one_unique (a e1 e2 : α) (h1 : is_one e1) (h2 : is_one e2) : e1 = e2 := by
  cases' h1 a with h1l h1r
  cases' h2 a with h2l h2r
  have h := h1r
  rw [←h2r] at h
  rw [mul_assoc] at h
  have q := And.left (h2 e1)
  rw [q] at h
  apply cancel_left a
  exact h

def is_inv (a b : α) := mul a b = one ∧ mul b a = one

theorem inv_unique (a b c : α) (h1 : is_inv a b) (h2 : is_inv a c) : b = c := by
  cases' h1 with h1l h1r
  cases' h2 with h2l h2r
  have h := h1r
  rw [←h2r] at h
  apply cancel_right a
  exact h

theorem inv_gh (g h : α) : is_inv (mul g h) (mul (inv h) (inv g)) := by
  apply And.intro

  rw [← mul_assoc]
  rw [mul_assoc g h _]
  rw [mul_right_inv]
  rw [mul_one]
  rw [mul_right_inv]

  rw [← mul_assoc]
  rw [mul_assoc (inv h) (inv g) _]
  rw [mul_left_inv]
  rw [mul_one]
  rw [mul_left_inv]

theorem inv_inv (a : α) : inv (inv a) = a := by
  have h : mul (inv (inv a)) (inv a) = one := by
    rw [mul_left_inv]
  have h2 : mul (mul (inv (inv a)) (inv a)) a = mul one a := by
    rw [h]
  have h3 : mul (inv (inv a)) (mul (inv a) a) = a := by
    rw [one_mul] at h2
    rw [mul_assoc] at h2
    exact h2
  rw [mul_left_inv] at h3
  rw [mul_one] at h3
  exact h3


def pow : α → Int → α :=
  fun g n =>
    match n with
    | Int.ofNat m => Nat.repeat (fun x => mul x g) m one
    | Int.negSucc m => inv (Nat.repeat (fun x => mul x g) m one)

instance : Pow α Int where
  pow := pow

macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : α) ($y : Int))

theorem pow_zero (a : α) : a ^ 0 = one := by
  rfl

instance : Mul α where
  mul := mul



postfix:max "⁻¹" => inv


theorem qwerty₁ (a : α) : (a⁻¹) * a = one := by
  rw [mul_left_inv]

#print qwerty₁


theorem pow_succ (a : α) (n : Nat) : a ^ (n + 1) = a ^ n * a := by
  rfl

variable (q : ℤ)
#check q

-- def order (a : α) : Nat :=
--   match Nat.find (fun n => pow a n = one) with
--   | none => 0
--   | some n => n + 1

end MyGroup

-- axiom mul_right_inv (a : α) : a * (inv a) = 1
