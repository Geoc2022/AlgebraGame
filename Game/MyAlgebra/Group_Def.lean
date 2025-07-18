import Mathlib.Tactic

namespace MyAlgebra

class One (α : Type) where
  /-- The element one -/
  one : α
@[inherit_doc]
notation "e" => One.one


class AbstactMagma (α : Type) where
  /-- The binary operation that must be closed by definition -/
  mul : α → α → α
@[inherit_doc]
infixl:70 " ⬝ "   => AbstactMagma.mul


class AbstactSemigroup (α : Type) extends AbstactMagma α where
  /-- The operation is associative -/
  mul_assoc : ∀ a b c : α, a ⬝ b ⬝ c = a ⬝ (b ⬝ c)

class AbstactUnitalMagma (α : Type) extends One α, AbstactMagma α where
  /-- Id is a left neutral element for the operation. -/
  one_mul : ∀ a : α, e ⬝ a = a
  /-- Id is a right neutral element for the operation -/
  mul_one : ∀ a : α, a ⬝ e = a


class AbstactMonoid (α : Type) extends AbstactSemigroup α, AbstactUnitalMagma α

class AbstactInv (α : Type) where
  /-- The inversion function -/
  inv : α → α
-- @[inherit_doc]
-- postfix:max "⁻¹" => AbstactInv.inv

class AbstactGroup (G : Type) extends AbstactMonoid G, AbstactInv G where
  inv_mul : ∀ a : G, inv a ⬝ a = e
  mul_inv : ∀ a : G, a ⬝ inv a = e
class AbstactCommGroup (G : Type) extends AbstactGroup G where
  mul_comm : ∀ a b : G, a ⬝ b = b ⬝ a
