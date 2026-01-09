import Game.Levels.PowGroup.L01_PowNegNat
import Game.Levels.PowGroup.L02_PowNegOne
import Game.Levels.PowGroup.L03_PowSucc
import Game.Levels.PowGroup.L04_PowPred
import Game.Levels.PowGroup.L05_PowAdd
import Game.Levels.PowGroup.L06_PowNeg
import Game.Levels.PowGroup.L07_PowSub
import Game.Levels.PowGroup.L08_PowMul



World "Group Power"
Title "Group Power World"

Introduction "
  A group consists of a set G together with a binary operation (`*`) we represent repeatedly multiplying an element by itself using `gpow`:

  ```
  def gpow {G : Type} [Group G] (x : G) : ℤ → G
  | Int.ofNat n => mpow x n
  | Int.negSucc n => mpow (x⁻¹) (n+1)
  ```
  To make it easier to work with, we've created the following lemmas:
    - `gpow_ofNat`: `g ^ ↑n = g ^ n`
    - `gpow_negSucc`: `g ^ (Int.negSucc n) = (g⁻¹) ^ (n+1)`
    - `gpow_zero`: `g ^ (0 : ℤ) = 1`
    - `gpow_one`: `g ^ (1 : ℤ) = g`
    - `inv_mpow`: `(g ^ n)⁻¹ = (g⁻¹) ^ n`

  They've also been added to `simp`
"
