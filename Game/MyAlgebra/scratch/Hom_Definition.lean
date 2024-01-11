import Game.MyAlgebra.Definition

namespace MyAlgebra

class Group_Hom (G H : Type) [Group G] [Group H] where
  /-- The function that must be a group homomorphism -/
  f : G → H
  /-- The function must preserve the group operation -/
  hom : ∀ a b : G, f (mul a b) = mul (f a) (f b)

export Group_Hom (hom)

-- infixr:25 " →* " => Group_Hom

def is_hom (f : G → H) [Group G] [Group H] := ∀ a b : G, f (mul a b) = mul (f a) (f b)
