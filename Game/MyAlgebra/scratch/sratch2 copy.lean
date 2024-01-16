import Mathlib.Tactic

namespace MyAlgebra

class Zero (α : Type) where
  /-- The element zero -/
  zero : α

class One (α : Type) where
  /-- The element one -/
  one : α

notation "e" => One.one

class AddMagma (α : Type) where
  /-- The binary operation that must be closed by definition -/
  add : α → α → α
infixl:65 " + "   => AddMagma.add

class Magma (α : Type) where
  /-- The binary operation that must be closed by definition -/
  mul : α → α → α
infixl:70 " ⬝ "   => Magma.mul


class AddSemigroup (α : Type) extends AddMagma α where
  /-- The operation is associative -/
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)

class Semigroup (α : Type) extends Magma α where
  /-- The operation is associative -/
  mul_assoc : ∀ a b c : α, a ⬝ b ⬝ c = a ⬝ (b ⬝ c)


class AddUnitalMagma (α : Type) extends Zero α, AddMagma α where
  /-- Zero is a left neutral element for the operation. -/
  zero_add : ∀ a : α, 0 + a = a
  /-- Zero is a right neutral element for the operation -/
  add_zero : ∀ a : α, a + 0 = a

class UnitalMagma (α : Type) extends One α, Magma α where
  /-- One is a left neutral element for the operation. -/
  one_mul : ∀ a : α, e ⬝ a = a
  /-- One is a right neutral element for the operation -/
  mul_one : ∀ a : α, a ⬝ e = a

class Monoid (α : Type) extends Semigroup α, UnitalMagma α

class Inv (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

class Group (G : Type) extends Monoid G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ ⬝ a = e
  mul_inv : ∀ a : G, a ⬝ a⁻¹ = e

class CommGroup (G : Type) extends Group G where
  mul_comm : ∀ a b : G, a ⬝ b = b ⬝ a


export One (one)
export Magma (mul)
export Semigroup (mul_assoc)
export UnitalMagma (one_mul mul_one)
export Inv (inv)
export Group (inv_mul mul_inv)
