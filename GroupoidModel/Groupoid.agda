{-# OPTIONS --allow-unsolved-metas #-}

module GroupoidModel.Groupoid where

open import Function using (const ; _$_)
open import Utils
open import Cubical.Core.Prelude
open import CategoryTheory
open import Agda.Primitive using (lsuc ; _⊔_)

module _ {l} where

  isGroupoid : (C : Category {l} {l}) → Set _
  isGroupoid C = ∀{a b} → (f : Morph a b) → isIso C f
    where open Category C

  record Groupoid : Set (lsuc l) where
    -- no-eta-equality
    field
      cat : Category {l} {l}
      strct : isStrictCategory cat
      grpd : isGroupoid cat

  open Groupoid  
  open Category

  GObj : Groupoid -> Set l
  GObj G = Obj (cat G)
  
  GMorph : (G : Groupoid) -> GObj G -> GObj G -> Set l
  GMorph G x y = Morph (cat G) x y

  gid : (G : Groupoid) (x : GObj G) -> GMorph G x x
  gid G x = id (cat G) x

module _ {l} (A : Set l) (aset : isSet A) where

  -- discrete groupoid
  Δgrpd : Groupoid {l}
  Δgrpd = record { cat = Δ A aset ; strct = aset _ _
                 ; grpd = λ f → sym f , aset _ _ _ _ , aset _ _ _ _ }

module _ {l} (G H : Groupoid {l}) where

  gcross : Groupoid {l}
  gcross = record { cat = cross (cat G) (cat H)
                  ; strct = {!!}
                  ; grpd = λ { (f , g) → (fst (grpd G f) , fst (grpd H g)) , {!!} , {!!} }}
    where open Groupoid

module _ {l1 l2} where

  open Groupoid

  GrpdFunctor : (G : Groupoid {l1}) (H : Groupoid {l2}) → Set _
  GrpdFunctor G H = cat G ⟶ cat H

module _ {l} where

  open Groupoid
  open Functor
  open Category

  Grpd : Category
  Grpd = record
           { Obj = Groupoid {l}
           ; Morph = GrpdFunctor
           ; id = λ G → IdFunctor (cat G)
           ; _∘_ = λ F G → compFun _ _ _ G F
           ; id∘ = λ {I} {J} F → Functor-≡ _ _ _ _ refl
           ; ∘id = λ {I} {J} F → Functor-≡ _ _ _ _ refl
           ; ∘∘ = λ {I} {J} {K} {L} F G H → Functor-≡ _ _ _ _ refl
           ; hom-set = λ {G} {H} → functIsSet (cat G) (cat H) (strct G)
           }

substMorph : ∀{l l'} {C : Category {l} {l'}} {a b c : Category.Obj C}
           -> a ≡ b -> Category.Morph C a c -> Category.Morph C b c
substMorph {C = C} p u = subst (λ z → Category.Morph C z _) p u

module _ {l} {l'} where
  open Groupoid
  open Functor
  open Category
  
  g-id : (G : Groupoid {l}) {x y : Obj (cat G)} (A : cat G ⟶ Grpd {l'}) (p : Morph (cat G) x y) (a : _)
      -> Morph (cat ((A ₀) y)) ((((A ₁) p) ₀) ((((A ₁) (fst (grpd G p))) ₀) a)) a
  g-id G {x} {y} A p a =
    substMorph {C = C} (sym ((apF0 _ _ _ _ a $ ap (A ₁) $ snd (snd (grpd G p))) · apF0 _ _ _ _ a (fid A y)) · apF0 _ _ _ _ a (f∘ A p p-1)) (id C a)
    where p-1 = (fst (grpd G p))
          C = cat ((A ₀) y)

