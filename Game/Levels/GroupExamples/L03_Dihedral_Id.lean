import Game.MyAlgebra.Dihedral
import Game.Levels.GroupExamples.L02_Z_mod_mZ_Inv

open MyAlgebra


World "Group Examples"
Level 3

Title "Dihedral Group Identity"

namespace MyAlgebra

Introduction "
  We can consider n-gons and their symmetries, which form a group called the dihedral group. The dihedral group of order 2n, denoted D_n, consists of n rotations and n reflections.

  Here is a square with its vertices labeled (1,2,3,4) and its symmetries (rotations and reflections):

    1-----2
    |     |
    4-----3

  Rotations:
    0° (identity)      90°                180°               270°
    1-----2            4-----1            3-----4            2-----3
    |     |            |     |            |     |            |     |
    4-----3            3-----2            2-----1            1-----4

  Reflections:
    Vertical           Horizontal         Diagonal (\\)        Diagonal (/)
    2-----1            4-----3            1-----4             3-----2
    |     |            |     |            |     |             |     |
    3-----4            1-----2            2-----3             4-----1

  Each symmetry is an element of the dihedral group D₄.


  We define the dihedral group D_n as follows:
  ```
  inductive Dihedral (n : ℕ) : Type
    | r : ZMod n → Dihedral n
    | sr : ZMod n → Dihedral n
  ```
  The elements of D_n are either rotations (`r i`) or reflections (`sr i`), where i is an integer modulo n. `r` stands for rotation and `s` stands for reflection.

  In this level, we will prove that the identity element of the dihedral group D_n is the identity rotation, which does not change the polygon.
"

namespace Dihedral

variable {n : ℕ}

/--
`Dihedral_id` is a proof that the identity element of the dihedral group `D_n` is `r 0`.
-/
TheoremDoc MyAlgebra.Dihedral_id as "Dihedral_id" in "Group Examples"
Statement Dihedral_id (n : ℕ) (a : Dihedral n) : ∃ b : Dihedral n, mul a (r 0) = a ∧ mul (r 0) a = a := by
  use r 0
  Hint "Use the definition of multiplication in the dihedral group."
  induction a with
  | r i => simp [mul]
  | sr i => simp [mul]

Conclusion "Congrats!"
