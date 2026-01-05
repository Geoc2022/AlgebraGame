import Game.MyAlgebra.Z_mod_mZ
import Game.Levels.Group.L06_OneUnique

World "Group Examples"
Level 1

Title "Z mod mZ Identity"

namespace MyAlgebra

Introduction "
  The set of integers Z = {... , −2, −1, 0, 1, 2, . . .} is a group if we use addition as the group law. It is an example of group with infinitely many elements.

  What goes wrong if we try to use multiplication as the group law?

  The set of integers modulo m (denoted Z/mZ) forms a group with addition as the group law.

  Ex. Z/12Z = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} is the group of integers modulo 12, which we use on clocks. If it's 11am and you add 1 hour, the clock wraps back to the start and it becomes 0pm (or 12pm).

  In this level, we will prove that the identity element of the group Z_mod_mZ is 0.
"

/--
`Z_mod_mZ_id` is a proof that the identity element of the group `Z_mod_mZ` is `0`.
-/
TheoremDoc MyAlgebra.Z_mod_mZ_id as "Z_mod_mZ_id" in "Group Examples"
Statement Z_mod_mZ_id (m : ℕ) (a : ZMod m) : 0 + a = a ∧ a + 0 = a := by
  Hint "We can use `add_zero` and `zero_add` from the Natural numbers."
  rw [add_zero, zero_add]
  exact ⟨rfl, rfl⟩

Conclusion "Congrats!"
