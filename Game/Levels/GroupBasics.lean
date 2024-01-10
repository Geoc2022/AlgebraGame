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
  This world works with basic group theorems that will be useful later.

  By the way, the way we define group is using Classes:

  We first create:
  Class (One) with an identity
    - one
  Class (Magma) with a binary operation
    - mul
  Class (Inv) with an inverse operation
    - inv

  Then we define:
  Class (Semigroup) extending the Magma with an associative binary operation
    - mul_assoc
  Class (Unital Magma) extending One, Magma with an identity (one)
    - mul_one
    - one_mul
  Class (Monoid) extending Unital Magma, Semigroup
    - mul_assoc
    - mul_one
    - one_mul

  Finally we define:
  Class (Group) extending Monoid, Inv
    - mul_assoc
    - mul_one
    - one_mul
    - mul_inv
    - inv_mul
    - mul_inv

  You can now use everything in these classes for your proofs.
"
