import Game.Metadata
import Game.MyAlgebra.AddMul_Group_Def

World "GroupBasics"
Level 1

Title "Left Multiplication"

namespace MyAlgebra

Introduction "Just to get us warmed up, let's create some lemmas to make it easy to multiply."

/--
`mul_left` is a proof that if `g1 = g2`, then `h * g1 = h * g2` - basically `h * _` if a function.
-/
TheoremDoc MyAlgebra.mul_left as "mul_left" in "Group"

@[to_additive]
Statement mul_left (g : G) [Group G] : g1 = g2 → g * g1 = g * g2 := by
  intro h
  rw [h]


Conclusion "Congrats on your first proof! Now let's move on to the next level."


/--
## Summary

`rfl` proves goals of the form `X = X`.

In other words, the `rfl` tactic will close any goal of the
form `A = B` if `A` and `B` are *identical*.

`rfl` is short for \"reflexivity (of equality)\".

## Example:

If the goal looks like this:

```
x + 37 = x + 37
```

then `rfl` will close it. But if it looks like `0 + x = x` then `rfl` won't work, because even
though $0+x$ and $x$ are always equal as *numbers*, they are not equal as *terms*.
The only term which is identical to `0 + x` is `0 + x`.

## Details

`rfl` is short for \"reflexivity of equality\".
-/
TacticDoc rfl

/--
## Summary

If `h` is a proof of an equality `X = Y`, then `rw [h]` will change
all `X`s in the goal to `Y`s. It's the way to \"substitute in\".

## Variants

* `rw [← h]` (changes `Y`s to `X`s; get the back arrow by typing `\\left ` or `\\l`.)

* `rw [h1, h2]` (a sequence of rewrites)

* `rw [h] at h2` (changes `X`s to `Y`s in hypothesis `h2`)

* `rw [h] at h1 h2 ⊢` (changes `X`s to `Y`s in two hypotheses and the goal;
get the `⊢` symbol with `\\|-`.)

* `repeat rw [add_zero]` will keep changing `? + 0` to `?`
until there are no more matches for `? + 0`.

* `nth_rewrite 2 [h]` will change only the second `X` in the goal to `Y`.

### Example:

If you have the assumption `h : x = y + y` and your goal is
```
succ (x + 0) = succ (y + y)
```

then

`rw [add_zero]`

will change the goal into `succ x = succ (y + y)`, and then

`rw [h]`

will change the goal into `succ (y + y) = succ (y + y)`, which
can be solved with `rfl`.

### Example:

You can use `rw` to change a hypothesis as well.
For example, if you have two hypotheses
```
h1 : x = y + 3
h2 : 2 * y = x
```
then `rw [h1] at h2` will turn `h2` into `h2 : 2 * y = y + 3`.


## Common errors

* You need the square brackets. `rw h` is never correct.

* If `h` is not a *proof* of an *equality* (a statement of the form `A = B`),
for example if `h` is a function or an implication,
then `rw` is not the tactic you want to use. For example,
`rw [P = Q]` is never correct: `P = Q` is the theorem *statement*,
not the proof. If `h : P = Q` is the proof, then `rw [h]` will work.

## Details

The `rw` tactic is a way to do \"substituting in\". There
are two distinct situations where you can use this tactic.

1) Basic usage: if `h : A = B` is an assumption or
the proof of a theorem, and if the goal contains one or more `A`s, then `rw [h]`
will change them all to `B`'s. The tactic will error
if there are no `A`s in the goal.

2) Advanced usage: Assumptions coming from theorem proofs
often have missing pieces. For example `add_zero`
is a proof that `? + 0 = ?` because `add_zero` really is a function,
and `?` is the input. In this situation `rw` will look through the goal
for any subterm of the form `x + 0`, and the moment it
finds one it fixes `?` to be `x` then changes all `x + 0`s to `x`s.

Exercise: think about why `rw [add_zero]` changes the term
`(0 + 0) + (x + 0) + (0 + 0) + (x + 0)` to
`0 + (x + 0) + 0 + (x + 0)`

If you can't remember the name of the proof of an equality, look it up in
the list of lemmas on the right.

## Targetted usage

If your goal is `b + c + a = b + (a + c)` and you want to rewrite `a + c`
to `c + a`, then `rw [add_comm]` will not work because Lean finds another
addition first and swaps those inputs instead. Use `rw [add_comm a c]` to
guarantee that Lean rewrites `a + c` to `c + a`. This works because
`add_comm` is a proof that `?1 + ?2 = ?2 + ?1`, `add_comm a` is a proof
that `a + ? = ? + a`, and `add_comm a c` is a proof that `a + c = c + a`.

If `h : X = Y` then `rw [h]` will turn all `X`s into `Y`s.
If you only want to change the 37th occurrence of `X`
to `Y` then do `nth_rewrite 37 [h]`.
-/
TacticDoc rw

/--
## Summary

`repeat t` repeatedly applies the tactic `t`
to the goal. You don't need to use this
tactic, it just speeds things up sometimes.

## Example

`repeat rw [add_zero]` will turn the goal
`a + 0 + (0 + (0 + 0)) = b + 0 + 0`
into the goal
`a = b`.
-/
TacticDoc «repeat»

/--
## Summary

If `h : X = Y` and there are several `X`s in the goal, then
`nth_rewrite 3 [h]` will just change the third `X` to a `Y`.

## Example

If the goal is `2 + 2 = 4` then `nth_rewrite 2 [two_eq_succ_one]`
will change the goal to `2 + succ 1 = 4`. In contrast, `rw [two_eq_succ_one]`
will change the goal to `succ 1 + succ 1 = 4`.
-/
TacticDoc nth_rewrite

NewTactic rfl rw
NewHiddenTactic «repeat» nth_rewrite

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
