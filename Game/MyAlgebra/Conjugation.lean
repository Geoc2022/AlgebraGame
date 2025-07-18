import Game.MyAlgebra.AddMul_Group_Def
import Game.MyAlgebra.Group_Hom_Def

namespace MyAlgebra

def conjugate (g x : G) [Group G] : G := g * x * g⁻¹

theorem conj_hom {G : Type} [Group G] (g : G) : ∀ a b : G, conjugate g (a * b) = conjugate g a * conjugate g b := by
  intro a b
  unfold conjugate
  simp only [mul_assoc]
  rw[← mul_assoc (g⁻¹), inv_mul, one_mul]
