import Game.Levels.GroupHom.L04_HomCompHom
import Game.MyAlgebra.Ring_Def

namespace MyAlgebra

theorem mul_zero {R : Type} [Ring R] (a : R) : a * 0 = 0 := by
  have h : a * 0 = a * 0 + a * 0 :=
    calc a * 0 = a * (0 + 0) := by rw [add_zero]
      _ = a * 0 + a * 0 := by rw [distrib_left]
  apply add_left_cancel (a * 0)
  rw [← h]
  rw [add_zero]

theorem zero_mul {R : Type} [Ring R] (a : R) : 0 * a = 0 := by
  have h : 0 * a = 0 * a + 0 * a :=
    calc 0 * a = (0 + 0) * a := by rw [zero_add]
      _ = 0 * a + 0 * a := by rw [distrib_right]
  apply add_left_cancel (0 * a)
  rw [← h]
  rw [add_zero]

theorem neg_mul {R : Type} [Ring R] (a b : R) : (-a) * (-b) = a * b := by
  have h1 : -(a * b) = (-a) * b := by
    apply add_right_cancel (a * b)
    rw [neg_add]
    rw [← distrib_right]
    rw [neg_add]
    rw [zero_mul]
  have h2 : -(a * b) = a * (-b) := by
    apply add_right_cancel (a * b)
    rw [neg_add]
    rw [add_comm]
    rw [← distrib_left]
    rw [add_neg]
    rw [mul_zero]
  have h3 : (a + -a) * (b + -b) = a * b + ((-a) * b) + (a * (-b)) + ((-a) * (-b)) := by
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
