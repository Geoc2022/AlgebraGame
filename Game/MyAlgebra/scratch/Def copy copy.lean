import Mathlib.Tactic.ScopedNS

class One (α : Type) where
  /-- The element one -/
  one : α

@[inherit_doc]
scoped[Group] notation "e" => One.one

def One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

scoped[Ring] attribute [instance] One.toOfNat1

class Zero (α : Type) where
  /-- The element zero -/
  zero : α

instance Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

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


class CommGroup (G : Type) extends Group G where
  mul_comm : ∀ a b : G, a ⬝ b = b ⬝ a

class Ring (R : Type) extends AddMonoid R, Monoid R where
  mul_add : ∀ a b c : R, a ⬝ (b + c) = a ⬝ b + a ⬝ c
  add_mul : ∀ a b c : R, (a + b) ⬝ c = a ⬝ c + b ⬝ c

section
open scoped Group

-- In a group theory context, you probably want to use `e` as your identity
theorem test₁ {G : Type} [Group G] (a : G) : a ⬝ e = a := by
  sorry

end

section
open scoped Ring

-- In a ring theory context, you probably want to use `1` as your identity
theorem test₂ {R : Type} [Ring R] (a : R) : a ⬝ 1 = a := by
  sorry

end
