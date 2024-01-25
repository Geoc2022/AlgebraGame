import Game.MyAlgebra.AddMul_Group_Def

namespace MyAlgebra

structure GroupHom (G H : Type) [Group G] [Group H] where
  /-- The function that must be a group homomorphism -/
  toFun : G → H
  /-- The function must preserve the group operation -/
  hom : ∀ a b : G, toFun (a * b) = (toFun a) * (toFun b)

instance [Group G] [Group H] : CoeFun (GroupHom G H) (fun _ ↦ G → H) where
  coe := GroupHom.toFun

attribute [coe] GroupHom.toFun

export GroupHom (hom)
