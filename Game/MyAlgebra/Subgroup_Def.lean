import Game.MyAlgebra.AddMul_Group_Def

namespace MyAlgebra

class Submonoid (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

class Subgroup (S : Type) (G : Type) [Group G] [SetLike S G] extends Submonoid S G : Prop where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

class Kernel

structure Normal (S : Type) (G : Type) [Group G] [SetLike S G] extends Subgroup S G : Prop where
  normal : ∀ (s : S) {a : G}, a ∈ s → ∀ (g : G), g * a * g⁻¹ ∈ s
