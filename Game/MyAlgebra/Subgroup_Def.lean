import Game.MyAlgebra.AddMul_Group_Def

namespace MyAlgebra

-- -- class Submonoid (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
-- --   mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
-- --   one_mem : ∀ s : S, 1 ∈ s

-- -- class Subgroup (S : Type) (G : Type) [Group G] [SetLike S G] extends Submonoid S G : Prop where
-- --   inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

-- class Submonoid [Monoid M] (S : Set M) : Prop where
--   mul_mem : ∀ {a b : M}, a ∈ S → b ∈ S → a * b ∈ S
--   one_mem : 1 ∈ S

-- class Subgroup [Group G] (S : Set G) extends Submonoid S : Prop where
--   inv_mem : ∀ {a : G}, a ∈ S → a⁻¹ ∈ S

-- lemma test (S : Set G) [Group G] [Subgroup S] : 1 ∈ S := one_mem

-- -- lemma test [Group G] [SetLike S G] [Subgroup S G] : ∀ s : S, 1 ∈ s :=
-- --   sorry

@[ext]
structure Submonoid (M : Type) [Monoid M] where
  carrier : Set M
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier

instance [Monoid M] : SetLike (Submonoid M) M where
  coe := Submonoid.carrier
  coe_injective' := Submonoid.ext

class SubmonoidClass (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass (Submonoid M) M where
  mul_mem := Submonoid.mul_mem
  one_mem := Submonoid.one_mem


@[ext]
structure Subgroup (G : Type) [Group G] where
  carrier : Set G
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier

instance [Group G] : SetLike (Subgroup G) G where
  coe := Subgroup.carrier
  coe_injective' := Subgroup.ext

class SubgroupClass (S : Type) (G : Type) [Group G] [SetLike S G] extends SubmonoidClass S G : Prop where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance [Group G] : SubgroupClass (Subgroup G) G where
  mul_mem := Subgroup.mul_mem
  one_mem := Subgroup.one_mem
  inv_mem := Subgroup.inv_mem
