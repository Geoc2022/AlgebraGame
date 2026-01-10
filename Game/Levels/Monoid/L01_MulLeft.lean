import Game.Metadata
import Game.MyAlgebra.AddMul_Group_Def

World "Monoid"
Level 1

Title "Left Multiplication"

namespace MyAlgebra

Introduction "Just to get us warmed up, let's create some lemmas for multiplication. We wil use the rewrite function to create a basic proof that multiplication is a function. In other words, if `m1 = m2`, then `m * m1 = m * m2` for any `m`. This could be useful if you want to use calc blocks later on."

/--
`mul_left` is a proof that if `m1 = m2`, then `m * m1 = m * m2` - basically `m * _` is a function.
-/
TheoremDoc MyAlgebra.mul_left as "mul_left" in "Monoid"
@[to_additive]
Statement mul_left {M} (m : M) {m1 m2 : M} [Monoid M] : m1 = m2 → m * m1 = m * m2 := by
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

/--
The `Iff.intro` tactic is used to prove a goal of the form `P ↔ Q`. It splits the goal into two subgoals: `P → Q` and `Q → P`.
-/
TacticDoc Iff.intro

/--
The `constructor` tactic can be used to prove goals that are inductive types with a single constructor. For example, it can be used to prove `P ↔ Q` by proving `P → Q`, or to prove `P ∧ Q` by splitting the goal into proving `P` and `Q`.
-/
TacticDoc «constructor»

/--
If `h : X = Y` and there are several `X`s in the goal, then `nth_rw 3 [h]` will just change the third `X` to a `Y`.
-/
TacticDoc nth_rw

/--
`cases' h with h1 h2 ... hn` is a tactic that splits `h` into cases and adds them as hypotheses `h1 h2 ... hn`
-/
TacticDoc cases'

/--
`use h` is a tactic used to provide a proof of a type using construction.
-/
TacticDoc use

NewTactic rfl rw intro apply «have» obtain «calc» exact simp «repeat» nth_rewrite Iff.intro «constructor» nth_rw cases' use
end Basic_Tactics

section Monoid_Axioms
/--
`mul_one` is a proof that for all `m : M`, `1 * m = m` (Left Identity Axiom).
-/
TheoremDoc mul_one as "mul_one" in "Monoid"
/--
`one_mul` is a proof that for all `m : M`, `m * 1 = m` (Right Identity Axiom).
-/
TheoremDoc one_mul as "one_mul" in "Monoid"

/--
`mul_assoc` is a proof that for all `m1 m2 m3 : M`, `(m1 * m2) * m3 = m1 * (m2 * m3)` (Associative Law).
-/
TheoremDoc MyAlgebra.Semigroup.mul_assoc as "mul_assoc" in "Monoid"
end Monoid_Axioms

/--
`And.left` and `And.right` are theorems that split an `And` into its left and right components
-/
TheoremDoc And.left as "And.left" in "Basic"
/--
`And.left` and `And.right` are theorems that split an `And` into its left and right components
-/
TheoremDoc And.right as "And.right" in "Basic"

/--
`And.intro` is a theorem that takes two proofs `h1 : P` and `h2 : Q` and returns a proof `h : P ∧ Q`
-/
TheoremDoc And.intro as "And.intro" in "Basic"

NewTheorem mul_one one_mul MyAlgebra.Semigroup.mul_assoc And.left And.right And.intro
