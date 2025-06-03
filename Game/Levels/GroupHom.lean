import Game.Levels.GroupHom.L01_HomPreservesOne
import Game.Levels.GroupHom.L02_HomPreservesInv
import Game.Levels.GroupHom.L03_IdHom
import Game.Levels.GroupHom.L04_OneHom
import Game.Levels.GroupHom.L05_HomCompHom

World "GroupHom"
Title "Group Homomorphisms"

Introduction "
  After creating groups, it's a good idea to define a function between them. There can be a lot of different functions between groups, but we only care about the ones that preserve the group structure (becasue they are the only interesting ones). These functions are called homomorphisms.

  So what makes up the group structure? Well, we have a set `α`, a binary operation `*`, an identity element `1`, and inverses. Therefore, we need to define a function that preserves these aspects.

  It turns out that we only need the binary operation to be preserved. And in the next two levels we get the other two for free.
"
