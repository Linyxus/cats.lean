import Cats.Core

namespace Cats

structure Inverse (C : Category O F) (f : F A B) where
  inverse : F B A
  leftId : C.comp inverse f = C.id B
  rightId : C.comp f inverse = C.id A

structure Isomorphism (C : Category O F) (A B : O) where
  forward : F A B
  backward : Inverse C forward

namespace Isomorphism

theorem inverse_data_eq {g1 g2 : Inverse C f} :
  g1.inverse = g2.inverse ->
  g1 = g2 := by
  intros h
  cases g1; cases g2
  simp at h; simp [h]

/-- Inverse of an arrow is unique.

  Proof sketch:

    g1 = g1 ∘ id
       = g1 ∘ (f ∘ g2)
       = (g1 ∘ f) ∘ g2
       = id ∘ g2
       = g2
-/
theorem inverse_is_unique : ∀ {C : Category O F} {f : F A B},
  (g1 : Inverse C f) ->
  (g2 : Inverse C f) ->
  g1 = g2 := by
  intros C f g1 g2
  apply inverse_data_eq
  rw [<- C.rightId (f := g1.inverse)]
  rw [<- g2.rightId]
  rw [<- C.assoc]
  rw [g1.leftId]
  rw [C.leftId]

end Isomorphism

end Cats
