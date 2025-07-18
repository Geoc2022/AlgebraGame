import Game.Metadata
import Game.MyAlgebra.AddMul_Group_Def

World "Group"
Level 1

Title "Left Multiplication"

namespace MyAlgebra

Introduction "Just to get us warmed up, let's create some lemmas for multiplication. We wil use the rewrite function to create a basic proof that multiplication is a function. In other words, if `g1 = g2`, then `h * g1 = h * g2` for any `h`. This could be useful if you want to use calc blocks later on."

/--
`mul_left` is a proof that if `g1 = g2`, then `h * g1 = h * g2` - basically `h * _` is a function.
-/
TheoremDoc MyAlgebra.mul_left as "mul_left" in "Group"
@[to_additive]
Statement mul_left (g : G) [Group G] : g1 = g2 → g * g1 = g * g2 := by
  Hint "Start by introducing the hypothesis with `intro`."
  intro h
  Hint "Now, use `rw` to rewrite the goal using the hypothesis `{h}`."
  rw [h]


Conclusion "Congrats on your first proof! Now let's move on to the next level."

section Basic_Tactics
/--
`rfl` proves goals of the form `X = X`.
-/
TacticDoc rfl

/--
If `h` is a proof of an equality `X = Y`, then `rw [h]` will change
all `X`s in the goal to `Y`s. It's the way to \"substitute in\".
-/
TacticDoc rw

/--
`intro h` will move a hypothesis from the goal to a new hypothesis called `h`.
-/
TacticDoc intro

/--
`apply h` will try to match the current goal against the conclusion of `h`,
-/
TacticDoc apply


/--
`have q : r := p` will add a new hypothesis called `q` with type `r` to the local context. It will need a proof `p`. Where you can use `by` to start a proof.
-/
TacticDoc «have»


/--
`obtain ⟨x, y, z⟩ := h` will destructure `h` into the variables `x`, `y`, and `z`. This is useful for when you have a hypothesis that is a tuple or a structure. You can type `⟨` using `\langle` and `⟩` using `\rangle`.
-/
TacticDoc obtain


/--
`calc` is a way to chain equalities together. It's a bit like `rw`, but you can see the whole chain of reasoning.
-/
TacticDoc «calc»


/--
`exact h` will close the goal if `h` is a proof of the goal.
-/
TacticDoc exact


/--
`simp` is a magic tactic that tries lots of different things to simplify your goal.
-/
TacticDoc simp


/--
`repeat t` repeatedly applies the tactic `t` to the goal. You don't need to use thistactic, it just speeds things up sometimes.
-/
TacticDoc «repeat»

/--
If `h : X = Y` and there are several `X`s in the goal, then `nth_rewrite 3 [h]` will just change the third `X` to a `Y`.
-/
TacticDoc nth_rewrite

NewTactic rfl rw intro apply «have» obtain «calc» exact simp «repeat» nth_rewrite
end Basic_Tactics

section Group_Axioms
/--
`mul_one` is a proof that for all `g : G`, `1 * g = g` (Left Identity Axiom).
-/
TheoremDoc mul_one as "mul_one" in "Group"
/--
`one_mul` is a proof that for all `g : G`, `g * 1 = g` (Right Identity Axiom).
-/
TheoremDoc one_mul as "one_mul" in "Group"

/--
`inv_mul` is a proof that for all `g : G`, `g⁻¹ * g = 1` (Left Inverse Axiom).
-/
TheoremDoc MyAlgebra.Group.inv_mul as "inv_mul" in "Group"

/--
`mul_assoc` is a proof that for all `g1 g2 g3 : G`, `(g1 * g2) * g3 = g1 * (g2 * g3)` (Associative Law).
-/
TheoremDoc MyAlgebra.Semigroup.mul_assoc as "mul_assoc" in "Group"
end Group_Axioms

NewTheorem mul_one one_mul MyAlgebra.Group.inv_mul MyAlgebra.Semigroup.mul_assoc
