import Game.MyAlgebra.Z_mod_mZ

namespace MyAlgebra

inductive Dihedral (n : ℕ) : Type
  | r : ZMod n → Dihedral n
  | sr : ZMod n → Dihedral n
  deriving DecidableEq

namespace Dihedral

variable {n : ℕ}

def mul : Dihedral n → Dihedral n → Dihedral n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)
  instance : Mul (Dihedral n) where
    mul := mul
