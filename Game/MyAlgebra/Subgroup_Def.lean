import Game.Levels.Group

namespace MyAlgebra

@[ext]
structure Subgroup (G : Type) [Group G] where
  carrier : Set G
  one_mem : 1 ∈ carrier
  mul_closure : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_closure : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier

variable {G : Type} [Group G]


instance : Coe (Subgroup G) (Set G) := ⟨λ H ↦ H.carrier⟩
instance : CoeSort (Subgroup G) (Type _) := ⟨λ H ↦ H.carrier⟩
instance : Membership G (Subgroup G) := ⟨λ g H ↦ g ∈ H.carrier⟩

attribute [coe] Subgroup.carrier

instance {H : Subgroup G} : Group H where
  mul := λ ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a * b, H.mul_closure ha hb⟩
  mul_assoc := by intros; ext; apply mul_assoc
  one := ⟨1, H.one_mem⟩
  one_mul := by intros; ext; apply one_mul
  mul_one := by intros; ext; apply mul_one
  inv := λ ⟨a, ha⟩ ↦ ⟨a⁻¹, H.inv_closure ha⟩
  inv_mul := by intros; ext; apply inv_mul
  mul_inv := by intros; ext; apply mul_inv

/--
1. H ≠ ∅
2. for all x, y ∈ H, x * (y⁻¹) ∈ H
-/
def Subgroup_Criterion (S : Set G) (he : ∃ (s : G), s ∈ S)
(hc : ∀ (x y : G), x ∈ S → y ∈ S → (x * (y⁻¹)) ∈ S)
: Subgroup G where
  carrier := S
  one_mem := by
    obtain ⟨s, hs⟩ := he
    rw [← mul_inv s]
    apply hc <;> exact hs
  inv_closure := by
    intro a
    have hc2 := hc
    rw [← one_mul (a⁻¹)]
    apply hc2 1 a
    have h1 : 1 ∈ S := by
      obtain ⟨s, hs⟩ := he
      rw [← mul_inv s]
      apply hc <;> exact hs
    exact h1
  mul_closure := by
    intro a b ha hb
    have hc3 := hc
    have hc4 := hc
    specialize hc3 a (b⁻¹)
    rw [← inv_inv b] at hc3
    have hf : b ∈ S → b⁻¹ ∈ S := by
      intro hb
      rw [←one_mul (b⁻¹)]
      apply hc4 1 b
      have h1 : 1 ∈ S := by
        obtain ⟨s, hs⟩ := he
        rw [← mul_inv s]
        apply hc <;> exact hs
      exact h1
      exact hb
    apply hf at hb
    apply hc3 at ha
    apply ha at hb
    exact hb
