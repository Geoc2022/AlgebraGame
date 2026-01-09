import Game.Levels.Group.L01_MulInv
import Game.Levels.Group.L02_CancelLeft
import Game.Levels.Group.L03_CancelRight
import Game.Levels.Group.L04_InvUnique
import Game.Levels.Group.L05_CombinedInv
import Game.Levels.Group.L06_CombinedInv2
import Game.Levels.Group.L07_InvId
import Game.Levels.Group.L08_InvInv
import Game.Levels.Group.L09_InvInj


World "Group"
Title "Group World"

Introduction "
  A group consists of a set G together with a binary operation (`*`) satisfying the following axioms:

  #### Identity Axiom
  There is an element `1 ∈ G` such that

    - mul_one : ∀ g : G, 1 * g = g
    - one_mul : ∀ g : G, g * 1 = g

  The element 1 is called the identity element of G.

  #### Inverse Axiom
  For every `g ∈ G` there is an element `h ∈ G` such that

    - mul_inv : ∀ g : G, g * g⁻¹ = 1
    - inv_mul : ∀ g : G, g⁻¹ * g = 1

  The element `h` is denoted `g⁻¹` (written \"g\\inv\") and is called the inverse of g.

  #### Associative Law
  For all `g1, g2, g3 ∈ G`, the associative law holds:

    - mul_assoc : ∀ g1 g2 g3 : G, (g1 * g2) * g3 = g1 * (g2 * g3)

"
