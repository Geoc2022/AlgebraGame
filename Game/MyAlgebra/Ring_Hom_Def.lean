import Game.MyAlgebra.Ring_Def

namespace MyAlgebra

structure RingHom (R S : Type) [Ring R] [Ring S] where
  /-- The function that must be a ring homomorphism -/
  toFun : R → S
  /-- The function must preserve the addition operation -/
  add_hom : ∀ a b : R, toFun (a + b) = (toFun a) + (toFun b)
  /-- The function must preserve the multiplication operation -/
  mul_hom : ∀ a b : R, toFun (a * b) = (toFun a) * (toFun b)
  /-- The function must preserve the multiplicative identity -/
  id_hom : toFun (1) = 1

instance [Ring R] [Ring S] : CoeFun (RingHom R S) (fun _ ↦ R → S) where
  coe := RingHom.toFun

attribute [coe] RingHom.toFun
