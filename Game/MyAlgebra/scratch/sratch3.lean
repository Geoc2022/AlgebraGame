import Game.MyAlgebra.Group_Hom_Def

namespace MyAlgebra

def injective {P Q : Type} (f : P → Q) : Prop := ∀ p1 p2 : P, f p1 = f p2 → p1 = p2

def surjective {P Q : Type} (f : P → Q) : Prop := ∀ q : Q, ∃ p : P, f p = q



theorem injectitive_iff_ker_eq_id {G H : Type} [Group G] [Group H] (f : GroupHom G H) : injective f ↔ f = 1 := by
  apply Iff.intro
  intro h
