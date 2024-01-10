import Game.MyAlgebra.AddMul_Group_Def

namespace MyAlgebra

class Ring (R : Type) extends AddCommGroup R, Monoid R :=
  distrib_left : ∀ a b c : R, a * (b + c) = a * b + a * c
  distrib_right : ∀ a b c : R, (a + b) * c = a * c + b * c

export Ring (distrib_left distrib_right)
