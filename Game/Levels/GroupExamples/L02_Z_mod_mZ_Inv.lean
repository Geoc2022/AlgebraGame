import Game.Levels.GroupExamples.L01_Z_mod_mZ_Id

World "Group Examples"
Level 2

Title "Z mod mZ Inverses"

namespace MyAlgebra

Introduction "
  In this level, we will prove that every element in the group `Z_mod_mZ` has an inverse.

  It might be helpful to use the `sub_eq_add_neg` and `sub_eq_neg_add` lemmas from the Natural numbers, which relate subtraction to addition with negation. Also, `sub_self` can be used to show that subtracting an element from itself gives zero.
"

/--
`Z_mod_mZ_inv` is a proof that the group `Z_mod_mZ` has an inverse for every element `a`.
-/
TheoremDoc MyAlgebra.Z_mod_mZ_inv as "Z_mod_mZ_inv" in "Group Examples"
Statement Z_mod_mZ_inv (m : ℕ) (a : ZMod m) : ∃ b : ZMod m, a + b = 0 ∧ b + a = 0 := by
  Hint "What is the inverse of an element in `Z_mod_mZ`?"
  use (-a : ZMod m)
  rw [← sub_eq_add_neg]
  rw [← sub_eq_neg_add]
  rw [sub_self]
  exact ⟨rfl, rfl⟩

Conclusion "Congrats!"
