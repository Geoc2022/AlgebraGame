import Game.Levels.GroupBasics.L01_MulLeft
import Game.Levels.GroupBasics.L02_MulRight
import Game.Levels.GroupBasics.L03_CancelLeft
import Game.Levels.GroupBasics.L04_CancelRight
import Game.Levels.GroupBasics.L05_OneUnique
import Game.Levels.GroupBasics.L06_InvUnique
import Game.Levels.GroupBasics.L07_CombinedInv
import Game.Levels.GroupBasics.L08_CombinedInv2
import Game.Levels.GroupBasics.L09_InvInv


World "GroupBasics"
Title "Group World"

Introduction "
  A group consists of a set G together with a binary operation (`*`) satisfying the following axioms:

  (a) (Identity Axiom) There is an element `1 ∈ G` such that
  - mul_one : ∀ g : G, 1 * g = g
  - one_mul : ∀ g : G, g * 1 = g
  The element 1 is called the identity element of G.

  (b) (Inverse Axiom) For every `g ∈ G` there is an element `h ∈ G` such that
  - mul_inv : ∀ g : G, g * g⁻¹ = 1
  - inv_mul : ∀ g : G, g⁻¹ * g = 1
  The element `h` is denoted `g⁻¹` (written \"g\\inv\") and is called the inverse of g.

  (c) (Associative Law) For all `g1, g2, g3 ∈ G`, the associative law holds:
  - mul_assoc : ∀ g1 g2 g3 : G, (g1 * g2) * g3 = g1 * (g2 * g3)

"
