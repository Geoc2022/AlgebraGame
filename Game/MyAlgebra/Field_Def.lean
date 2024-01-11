import Game.MyAlgebra.Ring_Def

namespace MyAlgebra

class Field (F : Type) extends CommRing F, Inv F :=
  mul_inv_cancel : ∀ a : F, a ≠ 0 → a * a⁻¹ = 1
  inv_mul_cancel : ∀ a : F, a ≠ 0 → a⁻¹ * a = 1

export Field (mul_inv_cancel inv_mul_cancel)
