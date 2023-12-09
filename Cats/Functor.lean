import Cats.Core
namespace Cats

structure Functor (C : Category O1 F1) (D : Category O2 F2) where
  mapObj : O1 -> O2
  mapArr : F1 a b -> F2 (mapObj a) (mapObj b)
  mapId : ∀ {a : O1}, mapArr (C.id a) = D.id (mapObj a)
  mapComp : ∀ {f : F1 a b} {g : F1 b c},
    mapArr (C.comp f g) = D.comp (mapArr f) (mapArr g)

end Cats
