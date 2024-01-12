import Game.Levels.GroupBasics.L01_MulLeft


World "RingBasics"
Title "Ring World"

Introduction "
  A ring is a set R together with two binary operations `+` and `*` satisfying the following axioms:

  The set R together with the binary operation `+` is an abelian group with identity element 0.
    (a) (Additive Identity Axiom) There is an element `0 ∈ R` such that
    - add_zero : ∀ r : R, 0 + r = r
    - zero_add : ∀ r : R, r + 0 = r

    (b) (Additive Inverse Axiom) For every `r ∈ R` there is an element `s ∈ R` such that
    - add_neg : ∀ r : R, r + (-r) = 0
    - neg_add : ∀ r : R, (-r) + r = 0

    (c) (Additive Associative Law) For all `r1, r2, r3 ∈ R`, the associative law holds:
    - add_assoc : ∀ r1 r2 r3 : R, (r1 + r2) + r3 = r1 + (r2 + r3)

    (d) (Additive Commutative Law) For all `r1, r2 ∈ R`, the commutative law holds:
    - add_comm : ∀ r1 r2 : R, r1 + r2 = r2 + r1

  The set R together with the binary operation `*` is a monoid with identity element 1.
    (a) (Multiplicative Identity Axiom) There is an element `1 ∈ R` such that
    - mul_one : ∀ r : R, 1 * r = r
    - one_mul : ∀ r : R, r * 1 = r

    (b) (Multiplicative Associative Law) For all `r1, r2, r3 ∈ R`, the associative law holds:
    - mul_assoc : ∀ r1 r2 r3 : R, (r1 * r2) * r3 = r1 * (r2 * r3)

  The two binary operations `+` and `*` satisfy the following distributive laws:
    (a) (Left Distributive Law) For all `r1, r2, r3 ∈ R`, the left distributive law holds:
    - mul_add : ∀ r1 r2 r3 : R, (r1 + r2) * r3 = (r1 * r3) + (r2 * r3)

    (b) (Right Distributive Law) For all `r1, r2, r3 ∈ R`, the right distributive law holds:
    - add_mul : ∀ r1 r2 r3 : R, r1 * (r2 + r3) = (r1 * r2) + (r1 * r3)
"
