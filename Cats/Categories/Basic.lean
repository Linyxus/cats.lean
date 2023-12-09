import Cats.Core
import Cats.Common
namespace Cats.Categories.Basic

namespace One

open Unit

inductive Arr : Unit -> Unit -> Type where
| arr : Arr unit unit
open Arr

instance : Category Unit Arr where
  comp _ _ := arr
  id _ := arr
  assoc := by simp
  leftId := by intros a b f; cases f; simp
  rightId := by intros a b f; cases f; simp

end One

namespace Two

inductive Bool : Type where
| yes : Bool
| no : Bool
open Bool

inductive Arr : Bool -> Bool -> Type where
| refl : ∀ b, Arr b b
| arr : Arr yes no
open Arr

def comp : Arr a b -> Arr b c -> Arr a c
| arr, refl _ => arr
| refl _, arr => arr
| refl _, refl _ => refl _

def assoc : ∀ (f : Arr a b) (g : Arr b c) (h : Arr c d),
  comp (comp f g) h = comp f (comp g h) := by
  intros f g h
  cases f <;> cases g <;> cases h <;> simp [comp]

theorem leftId : ∀ (f : Arr a b), comp (refl a) f = f := by
  intros f
  cases f <;> simp [comp, id]

theorem rightId : ∀ (f : Arr a b), comp f (refl b) = f := by
  intros f
  cases f <;> simp [comp, id]

instance : Category Bool Arr where
  comp := fun f g => comp f g
  id a := Arr.refl a
  assoc := by intros; simp [assoc]
  leftId := by intros; simp [leftId]
  rightId := by intros; simp [rightId]

end Two

namespace Three

inductive Obj : Type where
| one : Obj
| two : Obj
| three : Obj
open Obj

inductive Arr : Obj -> Obj -> Type where
| refl : ∀ a, Arr a a
| oneToTwo : Arr one two
| twoToThree : Arr two three
| oneToThree : Arr one three
open Arr

def comp : Arr a b -> Arr b c -> Arr a c
| refl _, arr => arr
| arr, refl _ => arr
| oneToTwo, twoToThree => oneToThree

theorem assoc : ∀ (f : Arr a b) (g : Arr b c) (h : Arr c d),
  comp (comp f g) h = comp f (comp g h) := by
  intros f g h
  cases f <;> cases g <;> cases h <;> simp [comp]

theorem leftId : ∀ (f : Arr a b), comp (refl a) f = f := by
  intros f
  cases f <;> simp [comp]

theorem rightId : ∀ (f : Arr a b), comp f (refl b) = f := by
  intros f
  cases f <;> simp [comp]

instance : Category Obj Arr where
  comp := fun f g => comp f g
  id a := Arr.refl a
  assoc := by intros; simp [assoc]
  leftId := by intros; simp [leftId]
  rightId := by intros; simp [rightId]

end Three

end Cats.Categories.Basic
