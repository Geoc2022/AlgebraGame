import Game.MyAlgebra.AddMul_Group_Def

namespace MyAlgebra

def Symmetric (n : ℕ) : Type := Fin n ≃ Fin n

instance (n : ℕ) : AbstactGroup (Symmetric n) where
  mul := Equiv.trans
  mul_assoc := λ _ _ _ ↦ rfl
  one := Equiv.refl (Fin n)
  one_mul := λ _ ↦ rfl
  mul_one := λ _ ↦ rfl
  inv := Equiv.symm
  inv_mul := by
    intro f
    dsimp [One]
    rw [←Equiv.coe_inj]
    funext x
    rw [Equiv.symm_trans_self, Equiv.refl_apply]
  mul_inv := by
    intro f
    dsimp [One]
    rw [←Equiv.coe_inj]
    funext x
    rw [Equiv.self_trans_symm, Equiv.refl_apply]
