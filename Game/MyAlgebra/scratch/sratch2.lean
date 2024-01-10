import Mathlib.Tactic

namespace MyAlgebra

class One (α : Type) where
  /-- The element one -/
  one : α

notation "e" => One.one

class Magma (α : Type) where
  /-- The binary operation that must be closed by definition -/
  mul : α → α → α

infixl:70 " ⬝ "   => Magma.mul

class Semigroup (α : Type) extends Magma α where
  /-- The operation is associative -/
  mul_assoc : ∀ a b c : α, a ⬝ b ⬝ c = a ⬝ (b ⬝ c)


class UnitalMagma (α : Type) extends One α, Magma α where
  /-- One is a left neutral element for the operation. -/
  one_mul : ∀ a : α, e ⬝ a = a
  /-- One is a right neutral element for the operation -/
  mul_one : ∀ a : α, a ⬝ e = a

class Monoid (α : Type) extends Semigroup α, UnitalMagma α

class Inv (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

class Group (G : Type) extends Monoid G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ ⬝ a = e
  mul_inv : ∀ a : G, a ⬝ a⁻¹ = e

export One (one)
export Magma (mul)
export Semigroup (mul_assoc)
export UnitalMagma (one_mul mul_one)
export Inv (inv)
export Group (inv_mul mul_inv)


variable {α : Type} [Group α]

def is_one (g : M) [UnitalMagma M] := ∀ a : M, mul g a = a ∧ mul a g = a

theorem mul_left (h : α) : g1 = g2 → mul h g1 = mul h g2 := by
  intro h1
  rw [h1]

theorem mul_right (h : α) : g1 = g2 → mul g1 h = mul g2 h := by
  intro h1
  rw [h1]

theorem cancel_left (h : α) : mul h g1 = mul h g2 → g1 = g2 := by
  intro h1
  have q := mul_left (inv h) h1
  rw [←mul_assoc] at q
  rw [inv_mul] at q
  rw [←mul_assoc] at q
  rw [inv_mul] at q
  rw [one_mul] at q
  rw [one_mul] at q
  exact q

theorem cancel_right (h : α) : mul g1 h = mul g2 h → g1 = g2 := by
  intro h1
  have q := mul_right (inv h) h1
  rw [mul_assoc] at q
  rw [mul_inv] at q
  rw [mul_assoc] at q
  rw [mul_inv] at q
  rw [mul_one] at q
  rw [mul_one] at q
  exact q

theorem one_unique (a e1 e2 : α) (h1 : is_one e1) (h2 : is_one e2) : e1 = e2 := by
  cases' h1 a with h1l h1r
  cases' h2 a with h2l h2r
  have h := h1r
  rw [←h2r] at h
  rw [mul_assoc] at h
  have q := And.left (h2 e1)
  rw [q] at h
  apply cancel_left a
  exact h

def is_inv (a b : G) [Group G] := mul a b = one ∧ mul b a = one

def is_inv' (a b : G) [Group G] := inv a = b

axiom inv_def (a b : α) : is_inv a b ↔ is_inv' a b

theorem inv_unique (a b c : α) (h1 : is_inv a b) (h2 : is_inv a c) : b = c := by
  cases' h1 with h1l h1r
  cases' h2 with h2l h2r
  have h := h1r
  rw [←h2r] at h
  apply cancel_right a
  exact h

theorem inv_prod (g h : α) : is_inv (mul g h) (mul (inv h) (inv g)) := by
  apply And.intro

  rw [← mul_assoc]
  rw [mul_assoc g h _]
  rw [mul_inv]
  rw [mul_one]
  rw [mul_inv]

  rw [← mul_assoc]
  rw [mul_assoc (inv h) (inv g) _]
  rw [inv_mul]
  rw [mul_one]
  rw [inv_mul]

-- instance : One ℕ :=
--   { one := 1 }

-- instance : Magma ℕ :=
--   { mul := Nat.mul }

-- def prod_list : List ℕ → ℕ
--   | [] => e
--   | (g::l) => mul g (prod_list l)

-- #eval prod_list [1, 2, 3] = 6

/--
  Given a list of elements of a group `G`, `prod_list` computes their product.

  If the list is empty, it returns the empty product - the identity element `e` of the group.
-/
def prod_list {G : Type} [Group G]: List G → G
  | [] => e
  | (g::l) => mul g (prod_list l)


/--
  Given a list of elements of a group `G`, `prod_list_inv` computes the product of the elements in the list in reverse order, with each element inverted.

  If the list is empty, it returns the empty product - the identity element `e` of the group.
-/
def prod_list_inv {G : Type} [Group G] : List G → G
  | [] => e
  | (a::l) => mul (prod_list_inv l) (inv a)

theorem inv_n_prod (l : List α) : is_inv (prod_list l) (prod_list_inv l) := by
  induction' l with fst rst

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
  rw [← mul_assoc _ _ (inv fst)]
  rw [tail_ih_l]
  rw [one_mul]
  rw [mul_inv]

  rw [mul_assoc]
  rw [← mul_assoc (inv fst)]
  rw [inv_mul]
  rw [one_mul]
  rw [tail_ih_r]


-- variable (g1 g2 g3 g4 g5 g6 : α)
-- variable (l : List α := [g1, g2, g3, g4, g5, g6])

-- def prod_list : ℕ → G
--   | 0 => G.one
--   | n + 1 => G.one

-- def prod_list_inv : List ℕ → ℕ
--   | [] => 1
--   | (a::l) => prod_list_inv l * a

-- #eval @prod_list α (g1) []

-- theorem inv_n_prod (l : List α) : is_inv (List.foldl mul e l) (List.foldr (fun x y => mul y (inv x)) e l) := by
--   induction' l with




theorem inv_inv (a : α) : inv (inv a) = a := by
  have h : mul (inv (inv a)) (inv a) = one := by
    rw [inv_mul]
  have h2 : mul (mul (inv (inv a)) (inv a)) a = mul one a := by
    rw [h]
  have h3 : mul (inv (inv a)) (mul (inv a) a) = a := by
    rw [one_mul] at h2
    rw [mul_assoc] at h2
    exact h2
  rw [inv_mul] at h3
  rw [mul_one] at h3
  exact h3


-- def pow : α → ℤ → α :=
--   fun g n =>
--     match n with
--     | Int.ofNat m => Nat.repeat (fun x => mul x g) m one
--     | Int.negSucc m => inv (Nat.repeat (fun x => mul x g) m one)

-- def pow₁ : α -> Nat -> α :=
--   fun g n => Nat.repeat (fun x => mul x g) n one

-- def pow₂ : α -> Int -> α :=
--   fun g n => match n with
--     | Int.ofNat m => Nat.repeat (fun x => mul x g) m one
--     | Int.negSucc m => inv (Nat.repeat (fun x => mul x g) m one)


-- inductive pow : α → Int → α
--   | zero : pow one 0
--   | succ (a : α) (n : Int) : pow a n → pow (a ⬝ a) (n - 1)
--   | pred (a : α) (n : Int) : pow a n → pow (inv a ⬝ inv a) (n + 1)


-- def lmul (g : α) : α ≃ α :=
--   { toFun := (mul) g, invFun := (mul) g⁻¹,
--     left_inv := by intro x; rw [← mul_assoc, inv_mul, one_mul]
--     right_inv := by intro x; rw [← mul_assoc, mul_inv, one_mul]}

-- def pow : α → ℤ → α :=
--   -- λ g n => (iterate n (lmul g)) e
--   λ g n => (lmul g)^[n] e


-- instance : Pow α Int where
--   pow := pow

-- macro_rules | `($x ^ $y)   => `(HPow.hPow ($x : α) ($y : Int))

-- theorem pow_zero (a : α) : a ^ 0 = one := by
--   rfl

-- theorem pow₁ (a : α) : a ^ (-1) ⬝ a = one := by
--   rw [pow]


class Group_Hom (G H : Type) [Group G] [Group H] where
  /-- The function that must be a group homomorphism -/
  f : G → H
  /-- The function must preserve the group operation -/
  hom : ∀ a b : G, f (mul a b) = mul (f a) (f b)

export Group_Hom (hom)

-- instance : Group_Hom α α where
--   f := id
--   hom := by
--     intro a b
--     rfl

variable {β : Type} [Group β]

def is_hom (f : α → β) := ∀ a b : α, f (mul a b) = mul (f a) (f b)

theorem hom_id : is_hom (id : α → α) := by
  intro a b
  rfl

theorem hom_one_to_one (f : α → β) (h : is_hom f) : f e = e := by
  have q := h e e
  rw [one_mul] at q
  apply cancel_right (f e)
  rw [one_mul]
  rw [←q]

theorem hom_inv_to_inv (f : α → β) (h : is_hom f) : (f a)⁻¹ = f (a⁻¹) := by
  have q := h a (a⁻¹)
  rw [mul_inv] at q
  rw [hom_one_to_one f h] at q
  apply cancel_left (f a)
  rw [mul_inv]
  rw [←q]

theorem hom_comp_hom (f1 : G → H) (f2 : H → J) [Group G] [Group H] [Group J] (h1 : is_hom f1) (h2 : is_hom f2) : is_hom (f2 ∘ f1) := by
  intro a b
  have q := h1 a b
  have r := h2 (f1 a) (f1 b)
  rw [← q] at r
  exact r


class group_isom (G H : Type) [Group G] [Group H] extends (Group_Hom G H) where
  /-- The function must be bijective -/
  f_inv : H → G
  /-- The function must preserve the group operation -/
  hom_inv : ∀ a b : H, f_inv (mul a b) = mul (f_inv a) (f_inv b)
  /-- The function must be bijective -/
  comp_inv_f : ∀ a : G, f_inv (f (a)) = a
  /-- The function must be bijective -/
  comp_f_inv : ∀ a : H, f (f_inv (a)) = a


instance : group_isom α α where
  f := id
  hom := hom_id
  f_inv := id
  hom_inv := hom_id
  comp_inv_f := by
    intro a
    rfl
  comp_f_inv := by
    intro a
    rfl
