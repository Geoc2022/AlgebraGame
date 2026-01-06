import Game.Levels.Group.L05_CombinedInv

World "Group"
Level 6

Title "Inverse of n Products"

namespace MyAlgebra

Introduction "We've seen that the inverse of a product of two elements is the product of the inverses in reverse order because of the anti-commutativity of the inverse operation. What about the inverse of a product of three elements? Or four? Or n?

We should expect it to follow the same pattern, and we can use induction to prove this. The inverse of a product of `n` elements is the product of the inverses in reverse order.

To make this a bit more formal, we defined a function `prod_list` that takes a list of elements of a group `G` and returns their product. We also define a function `prod_list_inv` that takes a list of elements of a group `G` and returns the product of the inverses of the elements in reverse order.

For example, if `l = [g1, g2, g3]` then `prod_list l = g1 ⬝ g2 ⬝ g3` and `prod_list_inv l = g3⁻¹ ⬝ g2⁻¹ ⬝ g1⁻¹`."

/--
  Given a list of elements of a group `G`, `prod_list` computes their product.

  If the list is empty, it returns the empty product - the identity element `e` of the group.
-/
DefinitionDoc MyAlgebra.prod_list as "prod_list"
def prod_list {G : Type} [Group G]: List G → G
  | [] => 1
  | (g::l) => g * (prod_list l)

/--
  Given a list of elements of a group `G`, `prod_list_inv` computes the product of the elements in the list in reverse order, with each element inverted.

  If the list is empty, it returns the empty product - the identity element `e` of the group.
-/
DefinitionDoc MyAlgebra.prod_list_inv as "prod_list_inv"
def prod_list_inv {G : Type} [Group G] : List G → G
  | [] => 1
  | (a::l) => (prod_list_inv l) * (a⁻¹)
NewDefinition MyAlgebra.prod_list MyAlgebra.prod_list_inv

/--
`inv_n_prod` is a proof that the inverse of a product of `n` elements is the product of the inverses in reverse order.
-/
-- TheoremDoc MyAlgebra.inv_n_prod as "inv_n_prod" in "Group"
-- Statement inv_n_prod (l : List G) [Group G] : is_inv (prod_list l) (prod_list_inv l) := by
Statement (l : List G) [Group G] : (prod_list_inv l) = (prod_list l)⁻¹ := by
  Hint "Since we're working with a generalized number of elements, it might be helpful to use induction. It also helps that the functions `prod_list` and `prod_list_inv` are defined recursively."
  apply inv_unique (prod_list l) (prod_list_inv l)
  induction' l with fst rst

  Hint "We can use the base cases in the definition of `prod_list` and `prod_list_inv` by using `rw [prod_list]` and `rw [prod_list_inv]`"
  rw [prod_list]
  rw [prod_list_inv]
  apply And.intro
  rw [mul_one]
  rw [one_mul]

  rw [prod_list]
  rw [prod_list_inv]
  cases' tail_ih with tail_ih_l tail_ih_r

  apply And.intro

  rw [mul_assoc]
  rw [← mul_assoc _ _ (fst⁻¹)]
  rw [tail_ih_l]
  rw [one_mul]
  rw [mul_inv]

  rw [mul_assoc]
  rw [← mul_assoc (fst⁻¹)]
  rw [inv_mul]
  rw [one_mul]
  rw [tail_ih_r]


Conclusion "Congrats!"

/--
`induction' l with fst rst` is a tactic that performs induction on the list `l`, with the first element of the list being called `fst` and the rest of the list being called `rst`.
-/
TacticDoc induction'

/--
```
induction l with
| nil => ...
| cons fst rst => ...
```
is a tactic that performs induction on the list `l`, with the first element of the list being called `fst` and the rest of the list being called `rst`.
-/
TacticDoc induction

NewTactic induction' induction
