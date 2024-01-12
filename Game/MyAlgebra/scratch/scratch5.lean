import Game.MyAlgebra.scratch.scratch4
import Game.MyAlgebra.Field_Def

namespace MyAlgebra


structure FieldHom (G H : Type) [Field G] [Field H] where
  /-- The function that must be a group homomorphism -/
  f : G → H
  /-- The function must preserve the group operation -/
  hom_mul : ∀ a b : G, f (a * b) = (f a) * (f b)
  hom_add : ∀ a b : G, f (a + b) = (f a) + (f b)

instance [Field G] [Field H] : CoeFun (FieldHom G H) (fun _ ↦ G → H) where
  coe := FieldHom.f

attribute [coe] FieldHom.f


theorem field_hom_inj [Field G] [Field H] (f : FieldHom G H) : ∀ a b : G, a ≠ b → f a ≠ f b := by
  intro a b h
  intro hf
  have q : a + -b ≠ 0 := by
    intro h'
    apply h
    apply add_right_cancel (-b)
    rw [add_neg]
    exact h'
  have q' : f (a + -b) = 0 := by
    have r := f.hom_add a (-b)
    rw [hf] at r
    have r' := f.hom_add b (-b)
    rw [← r'] at r
    rw [add_neg] at r
    have r'' : f 0 = 0 := by
      have s := f.hom_add 0 0
      rw [add_zero] at s
      apply add_right_cancel (f 0)
      rw [zero_add]
      rw [←s]
    rw [r''] at r
    exact r
  have q'' : ∀ c, f c = 0 → c = 0 := by
    intro c h'
    have s : f 1 = 1 := by
      have t := f.hom_mul 1 1
      rw [one_mul] at t
      have t' : ∀ g : H, g ≠ 0 → g = g * g → g = 1 := by
        intro g w w'
        have y := mul_inv_cancel g w
        sorry
    sorry
  apply q
  apply q'' (a + -b)
  exact q'
