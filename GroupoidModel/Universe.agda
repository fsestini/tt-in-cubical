{-# OPTIONS --allow-unsolved-metas #-}

module GroupoidModel.Universe {l} where

open import Cubical.Core.Prelude
open import CategoryTheory
open import GroupoidModel.Groupoid
open Category
open Groupoid
open import GroupoidModel.Basics

open import Agda.Primitive

Cat : Category {lsuc l} {lsuc l}
Obj Cat = Category {l} {l}
Morph Cat C D = Functor' C D
id Cat I₁ = {!!}
(Cat ∘ x) x₁ = {!!}
hom-set Cat x y x₁ y₁ = {!!}
id∘ Cat f = {!!}
∘id Cat f = {!!}
∘∘ Cat f g h = {!!}

open import Utils

GpdCat : Category {lsuc l} {lsuc l}
Obj GpdCat = Groupoid {l} -- {l}
Morph GpdCat G H = Σ (Functor' (cat G) (cat H)) (isIso Cat)
id GpdCat G = MkFunctor' (IdFunctor (cat G)) , {!!}
_∘_ GpdCat (MkFunctor' F , isoF) (MkFunctor' G , isoG) =
  MkFunctor' (compFun G F) , {!!}
hom-set GpdCat (MkFunctor' F , isoF) (MkFunctor' G , isoG) p q = {!!}
id∘ GpdCat (MkFunctor' f , isoF) = Σ-prop-≡ (λ F → {!!}) (ap MkFunctor' (Functor-≡ (FunctorEq-refl f)))
∘id GpdCat f = {!!}
∘∘ GpdCat f g h = {!!}

Gpd : Groupoid {lsuc l} -- {lsuc l}
Gpd = record { cat = GpdCat ; strct = {!!} ; grpd = {!!} }

module _ where
  open Functor
  open Functor'

  forgetIsos : Functor GpdCat (Grpd {l})
  (forgetIsos ₀) G = G
  (forgetIsos ₁) f = unFunctor' (fst f)
  fid forgetIsos _ = refl
  f∘  forgetIsos _ _ = refl

  incl : Functor GpdCat (Grpd {lsuc l})
  incl = compFun forgetIsos gliftFunctor

module _ {Γ : Groupoid {lsuc l}} where

  Univ : Ty Γ
  Univ = ConstFunctor _ _ Gpd

  open Functor
  open Tm

  El' : Tm Γ Univ -> Functor (cat Γ) GpdCat
  (El' A ₀) γ = (A ₀') γ
  (El' A ₁) p = (A ₁') p
  fid (El' A) γ = {!!}
  f∘  (El' A) = {!!}

  El : Tm Γ Univ -> Ty Γ
  El A = compFun (El' A) incl
