import Game.Levels.Monoid.L01_MulLeft
import Game.Levels.Monoid.L02_MulRight
import Game.Levels.Monoid.L03_OneUnique


World "Monoid"
Title "Monoid World"

Introduction "
  A monoid consists of a set M together with a binary operation (`*`) satisfying the following axioms:
  #### Identity Axiom
  There is an element `1 ∈ M` such that

    - mul_one : ∀ m : M, 1 * m = m
    - one_mul : ∀ m : M, m * 1 = m

  The element 1 is called the identity element of M.

  #### Associative Law
  For all `m1, m2, m3 ∈ M`, the associative law holds:

    - mul_assoc : ∀ m1 m2 m3 : M, (m1 * m2) * m3 = m1 * (m2 * m3)

"
