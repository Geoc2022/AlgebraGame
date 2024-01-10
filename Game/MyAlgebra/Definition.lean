import Mathlib.Tactic

namespace MyAlgebra

class One (α : Type) where
  /-- The element one -/
  one : α

@[inherit_doc]
notation "(1)" => One.one

@[inherit_doc]
notation "e" => One.one


class Zero (α : Type) where
  /-- The element zero -/
  zero : α

@[inherit_doc]
notation "(0)" => Zero.zero

-- @[inherit_doc]
-- notation "𝟬" => Zero.zero


class Magma (α : Type) where
  /-- The binary operation that must be closed by definition -/
  mul : α → α → α

@[inherit_doc]
infixl:70 " ⬝ "   => Magma.mul


class AddSemigroup (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

class Semigroup (α : Type) extends Magma α where
  /-- The operation is associative -/
  mul_assoc : ∀ a b c : α, a ⬝ b ⬝ c = a ⬝ (b ⬝ c)


class UnitalAddMagma (α : Type) extends Zero α, Add α where
  /-- One is a left neutral element for the operation. -/
  zero_add : ∀ a : α, (0) + a = a
  /-- One is a right neutral element for the operation -/
  add_zero : ∀ a : α, a + (0) = a

class UnitalMagma (α : Type) extends One α, Magma α where
  /-- One is a left neutral element for the operation. -/
  one_mul : ∀ a : α, e ⬝ a = a
  /-- One is a right neutral element for the operation -/
  mul_one : ∀ a : α, a ⬝ e = a


class AddMonoid (α : Type) extends AddSemigroup α, UnitalAddMagma α

class Monoid (α : Type) extends Semigroup α, UnitalMagma α


class Inv (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv


class AddGroup (α : Type) extends AddMonoid α, Neg α where
  neg_add : ∀ a : α, -a + a = (0)
  add_neg : ∀ a : α, a + -a = (0)


class Group (G : Type) extends Monoid G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ ⬝ a = e
  mul_inv : ∀ a : G, a ⬝ a⁻¹ = e

export One (one)
export Magma (mul)
export Semigroup (mul_assoc)
export UnitalMagma (one_mul mul_one)
export Inv (inv)
export Group (inv_mul mul_inv)


class CommGroup (G : Type) extends Group G where
  mul_comm : ∀ a b : G, a ⬝ b = b ⬝ a

export CommGroup (mul_comm)


def is_one (g : G) [Group G] := ∀ a : G, g ⬝ a = a ∧ a ⬝ g = a
def is_inv (a b : G) [Group G] := a ⬝ b = e ∧ b ⬝ a = e


class Ring (R : Type) extends AddMonoid R, Monoid R where
  mul_add : ∀ a b c : R, a ⬝ (b + c) = a ⬝ b + a ⬝ c
  add_mul : ∀ a b c : R, (a + b) ⬝ c = a ⬝ c + b ⬝ c

export Zero (zero)
export UnitalAddMagma (zero_add add_zero)
export Ring (mul_add add_mul)



class CommRing (R : Type) extends Ring R where
  mul_comm : ∀ a b : R, a ⬝ b = b ⬝ a

export CommRing (mul_comm)

def is_zero (g : R) [Ring R] := ∀ a : R, g ⬝ a = (0) ∧ a ⬝ g = (0)
def is_neg (a b : R) [Ring R] := a + b = (0) ∧ b + a = (0)

-- variable (R : Type) [Ring R]

-- #check ((0) : R) + ((0) : R) = (1)

-- theorem mul_zero [Ring R] (a : R) : a ⬝ (0) = (0) := by
--   have h1 : (1) + (0) = (1) := add_zero ((1) : R)
--   have h2 : a ⬝ ((1) + (0)) = a ⬝ (1) := by rw [h1]
--   calc
