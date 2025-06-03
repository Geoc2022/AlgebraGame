import Game.Levels.GroupExamples.L03_Dihedral_Id

World "Group Examples"
Level 4

Title "Z mod mZ Inverses"

namespace MyAlgebra

Introduction "
  In this level, we will prove that every element in the dihedral group has an inverse.
"

namespace Dihedral


/--
`Dihedral_inv` is a proof that the group `Z_mod_mZ` has an inverse for every element `a`.
-/
TheoremDoc MyAlgebra.Dihedral_inv as "Dihedral_inv" in "Group Examples"
Statement Dihedral_inv (n : ℕ) (a : Dihedral n) : ∃ b : Dihedral n, mul a b = (r 0) ∧ mul b a = (r 0) := by
  Hint "What is the inverse of an element in `Dihedral`? Dihedral elements are either rotations or reflections."
  induction a with
  | r i =>
    use (r (- i))
    simp [mul]
  | sr i =>
    use (sr i)
    simp [mul]

Conclusion "Congrats!"
