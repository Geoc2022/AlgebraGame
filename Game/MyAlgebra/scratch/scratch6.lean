import Game.MyAlgebra.Group_Hom_Def

namespace MyAlgebra

structure AbelGroupHom (G H : Type) [CommGroup G] [CommGroup H] where
  GroupHom : G → H

end MyAlgebra
