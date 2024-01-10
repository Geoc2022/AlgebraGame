import Game.MyAlgebra.AddMul_Group_Def

namespace MyAlgebra

structure GroupHom (G H : Type) [Group G] [Group H] where
  /-- The function that must be a group homomorphism -/
  f : G → H
  /-- The function must preserve the group operation -/
  hom : ∀ a b : G, f (a * b) = (f a) * (f b)

instance [Group G] [Group H] : CoeFun (GroupHom G H) (fun _ ↦ G → H) where
  coe := GroupHom.f

attribute [coe] GroupHom.f

export GroupHom (hom)

def is_hom {G H : Type} [Group G] [Group H] (f : G → H)  := ∀ a b : G, f (a * b) = (f a) * (f b)
