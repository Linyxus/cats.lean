import Cats.Core
namespace Cats
namespace Monoid

structure Monoid (A : Type u) where
  empty : A
  append : A → A → A
  assoc : ∀ {x y z}, append (append x y) z = append x (append y z)
  leftId : ∀ {x}, append empty x = x
  rightId : ∀ {x}, append x empty = x

namespace MonoidAsCat

inductive Unit : Type where
| unit : Unit

instance (m : Monoid A) : Category Unit (fun _ _ => A) where
  comp f g := m.append f g
  id _ := m.empty
  assoc := by simp [Monoid.assoc]
  leftId := by simp [Monoid.leftId]
  rightId := by simp [Monoid.rightId]

end MonoidAsCat

theorem catAsMonoid (C : Category O F) (c : O) : Monoid (F c c) := {
  empty := C.id c
  append := C.comp
  assoc := C.assoc
  leftId := C.leftId
  rightId := C.rightId
}

theorem homSetMonoid (X : Type u) : Monoid (X -> X) := {
  empty := id
  append := fun f g => f ∘ g
  assoc := by intros; simp; funext; simp
  leftId := by intros; simp; funext; simp
  rightId := by intros; simp; funext; simp
}

structure Homomorphism (M : Monoid A) (N : Monoid B) where
  map : A -> B

  mapComp : ∀ {x y}, map (M.append x y) = N.append (map x) (map y)
  mapId : map M.empty = N.empty

structure Monoid' where
  A : Type u
  inst : Monoid A

instance Mon : Category Monoid' (fun M N => Homomorphism M.inst N.inst) where
  comp f g := {
    map := fun x => g.map (f.map x)
    mapComp := by intros; simp [Homomorphism.mapComp]
    mapId := by intros; simp [Homomorphism.mapId]
  }
  id M := {
    map := fun x => x
    mapComp := by intros; simp
    mapId := by intros; simp
  }
  assoc := by intros; simp
  leftId := by intros; simp
  rightId := by intros; simp

end Monoid
end Cats
