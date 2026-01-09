import Game.Levels.PowMonoid.L01_PowOne
import Game.Levels.PowMonoid.L02_PowSuccLeft
import Game.Levels.PowMonoid.L03_PowAdd
import Game.Levels.PowMonoid.L04_PowMul
import Game.Levels.PowMonoid.L05_PowId
import Game.Levels.PowMonoid.L06_PowCommMul
import Game.Levels.PowMonoid.L07_PowCommPow


World "Monoid Power"
Title "Monoid Power World"

Introduction "
  A monoid consists of a set M together with a binary operation (`*`) we represent repeatedly multiplying an element by itself using `mpow` with the following definition:

    - `mpow_zero`: `m ^ 0 = 1`
    - `mpow_succ_right`: `m ^ (n + 1) = m ^ n * m`

  They've also been added to `simp`
"
