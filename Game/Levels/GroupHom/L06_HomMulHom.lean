import Game.Levels.GroupHom.L05_HomCompHom

World "BasicRing"
Level 6

Title "Homorphism Multiplied by a Homomorphism is a Homomorphism"

namespace MyAlgebra

Introduction "
  Along with the composition of two homomorphisms we can also multiply two homomorphisms to get a new homomorphism.

  We'll use a new theorem called `Pi.mul_apply` which defines how to multiply two functions:
  ```
  f * g (a) = f a * g a
  ```
"

/--
`hom_mul_hom` is a proof that a homomorphism multiplied by a homomorphism is a homomorphism.
-/
TheoremDoc MyAlgebra.hom_mul_hom as "hom_mul_hom" in "Ring"
Statement hom_mul_hom [CommGroup G] [CommGroup H] (f1 : GroupHom G H) (f2 : GroupHom G H) : GroupHom G H := by
  use f1 * f2
  intro a b
  have h1 := f1.hom a b
  have h2 := f2.hom a b
  rw [Pi.mul_apply]
  rw [Pi.mul_apply]
  rw [Pi.mul_apply]
  rw [h1, h2]
  rw [← mul_assoc]
  rw [mul_comm _ (f2 a)]
  rw [← mul_assoc]
  rw [mul_comm (f2 a)]
  rw [mul_assoc]

Conclusion "Congrats!"
