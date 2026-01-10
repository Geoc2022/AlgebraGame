import Game.Levels.Ring.L01_MulZero

World "Ring"
Level 2

Title "Multiplication of Negatives"

namespace MyAlgebra

Introduction "
  We've seen how the identity element of addition interacts with multiplication. Now we'll see how the additive inverse interacts with multiplication.
"

/--
`neg_mul` is a proof that `(-a) * (-b) = a * b`.
-/
TheoremDoc MyAlgebra.neg_mul as "neg_mul" in "Ring"
Statement neg_mul {R} [Ring R] (a b : R) : (-a) * (-b) = a * b := by
  have h1 : -(a * b) = (-a) * b := by
    apply add_right_cancel (a * b)
    rw [neg_add]
    rw [← distrib_right]
    rw [neg_add]
    rw [zero_mul]
  have h2 : -(a * b) = a * (-b) := by
    apply add_left_cancel (a * b)
    rw [add_neg]
    rw [← distrib_left]
    rw [add_neg]
    rw [mul_zero]
  have h3 : (a + -a) * (b + -b) = a * b + (-a) * b + a * (-b) + (-a) * (-b) := by
    rw [distrib_left]
    rw [distrib_right]
    rw [distrib_right]
    rw [← add_assoc]
  have h4 : (a + -a) * (b + -b) = 0 := by
    rw [add_neg]
    rw [zero_mul]

  apply add_right_cancel (-(a * b))
  rw [add_neg]
  rw [← h4]
  rw [h3]

  apply add_left_cancel (-(-a * -b))
  rw [← h1]
  rw [add_neg]
  rw [zero_add]
  rw [← h2]
  rw [add_comm _ (-a * -b)]

Conclusion "Congrats!"
