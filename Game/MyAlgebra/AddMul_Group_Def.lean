import Game.MyAlgebra.Group_Def

namespace MyAlgebra

class AddSemigroup (α : Type) extends Add α where
  /-- The operation is associative -/
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive]
class Semigroup (α : Type) extends Mul α where
  /-- The operation is associative -/
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)


class AddMonoid (α : Type) extends AddSemigroup α, AddZeroClass α where

@[to_additive]
class Monoid (α : Type) extends Semigroup α, MulOneClass α
attribute [to_additive existing] Monoid.toMulOneClass

class AddGroup (G : Type) extends AddMonoid G, Neg G where
  neg_add : ∀ a : G, -a + a = 0
  add_neg : ∀ a : G, a + -a = 0

@[to_additive]
class Group (G : Type) extends Monoid G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1
  mul_inv : ∀ a : G, a * a⁻¹ = 1


class AddCommGroup (G : Type) extends AddGroup G where
  add_comm : ∀ a b : G, a + b = b + a

@[to_additive]
class CommGroup (G : Type) extends Group G where
  mul_comm : ∀ a b : G, a * b = b * a

export AddSemigroup (add_assoc)
export Semigroup (mul_assoc)
export AddGroup (neg_add add_neg)
export Group (inv_mul mul_inv)
export AddCommGroup (add_comm)
export CommGroup (mul_comm)

end MyAlgebra
