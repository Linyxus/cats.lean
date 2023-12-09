import Cats.Core
namespace Cats

structure Group (A : Type u) where
  unit : A
  op : A → A → A
  inv : A → A

  leftId : op unit x = x
  rightId : op x unit = x
  assoc : op (op x y) z = op x (op y z)
  leftInv : op (inv x) x = unit
  rightInv : op x (inv x) = unit

namespace Group

def asCat (G : Group A) : Category Unit (fun _ _ => A) :=
  { comp := fun f g => G.op f g
  , id := fun _ => G.unit
  , leftId := by intros; simp [G.leftId]
  , rightId := by intros; simp [G.rightId]
  , assoc := by intros; simp [G.assoc]
  }

end Group

end Cats
