namespace Cats

structure Category (O : Type o) (F : O -> O -> Type f) where
  comp : (f : F a b) -> (g : F b c) -> F a c
  id : (a : O) -> F a a
  assoc : ∀ {f : F a b} {g : F b c} {h : F c d},
    comp (comp f g) h = comp f (comp g h)
  leftId : ∀ {f : F a b}, comp (id a) f = f
  rightId : ∀ {f : F a b}, comp f (id b) = f

end Cats
