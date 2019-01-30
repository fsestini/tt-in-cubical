{-# OPTIONS --allow-unsolved-metas #-}

module GroupoidModel.Universe {l} where

open import Cubical.Core.Prelude
open import CategoryTheory
open import GroupoidModel.Groupoid
open Category
open Groupoid

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

GpdCat : Category {lsuc l} {lsuc l}
Obj GpdCat = Groupoid {l} {l}
Morph GpdCat G H = Σ (Functor' (cat G) (cat H)) (isIso Cat)
id GpdCat I₁ = {!!}
(GpdCat ∘ x) x₁ = {!!}
hom-set GpdCat x y x₁ y₁ = {!!}
id∘ GpdCat f = {!!}
∘id GpdCat f = {!!}
∘∘ GpdCat f g h = {!!}

Gpd : Groupoid {lsuc l} {lsuc l}
Gpd = record { cat = GpdCat ; strct = {!!} ; grpd = {!!} }

incl : Functor GpdCat Grpd
incl = {!!}
