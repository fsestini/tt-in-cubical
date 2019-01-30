-- {-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --allow-unsolved-metas #-}

module GroupoidModel.Model where

open import GroupoidModel.Groupoid
open import GroupoidModel.Basics
-- open import GroupoidModel.PiTypes
open import Model
open import CategoryTheory
open import Cubical.Core.Prelude

open Model.Model
open Groupoid

module _ {l} {l'} where

  open import GroupoidModel.Universe {l}

  grpdModel : Model
  Conᴹ grpdModel = Groupoid
  Tmsᴹ grpdModel = GrpdFunctor
  Tyᴹ  grpdModel Γ = cat Γ ⟶ Grpd
  Tmᴹ  grpdModel Γ A = Tm Γ A
  _,ᴹ_ grpdModel Γ A = Γ ,, A
  -- π₁ᴹ  grpdModel {Γᴹ = record { cat = Γ }} σ =
  --   MkFunct (λ x → fst ((σ ₀) x))
  --           (λ f → fst ((σ ₁) f))
  --           (λ x → cong fst (fid σ x))
  --           λ f g → cong fst (f∘ σ f g)
  --   where open Functor
  -- _[_]ᴹ grpdModel = _[_]
  -- _[_]'ᴹ grpdModel = _[_]'
  -- _,sᴹ_ grpdModel {Γᴹ = record { cat = Δ }} {record { cat = Γ }} f M =
  --   MkFunct (λ δ → (f ₀) δ , (M ₀') δ)
  --           (λ u → (f ₁) u , (M ₁') u)
  --           (λ x → {!!}) {!!}
  --   where open Category ; open Functor ; open Tm
  -- π₂ᴹ  grpdModel {Γᴹ = Δ} {Γ} {Aᴹ = A} σ = π₂ σ

  -- ◇ᴹ grpdModel = {!!}
  -- idᴹ grpdModel Γᴹ = {!!}
  -- εᴹ grpdModel = {!!}
  -- εηᴹ grpdModel x = {!!}
  -- _∘ᴹ_ grpdModel x x₁ = {!!}
  -- [id]ᴹ grpdModel Aᴹ x = {!!}
  -- [][]ᴹ grpdModel x = {!!}
  -- id∘ᴹ grpdModel x = {!!}
  -- ∘idᴹ grpdModel x = {!!}
  -- ∘∘ᴹ grpdModel x = {!!}
  -- π₁βᴹ grpdModel x = {!!}
  -- π₂βᴹ grpdModel i = {!!}
  -- πηᴹ grpdModel x = {!!}
  -- ,∘₁ᴹ grpdModel x = {!!}
  -- _[_]'∘ᴹ grpdModel x σᴹ = {!!}
  -- [][]∘ᴹ grpdModel tᴹ σᴹ i = {!!}
  -- ,∘₂ᴹ grpdModel i = {!!}
  -- π₂∘ᴹ grpdModel σ = {!!}
  -- π₂≡ᴹ grpdModel σ i = {!!}
  Uᴹ grpdModel = ConstFunctor _ _ Gpd
  -- U[]ᴹ grpdModel σᴹ x = {!!}
  -- _[_]'Uᴹ grpdModel x σ = {!!}
  -- []U≡ᴹ grpdModel t σ i = {!!}
  -- Πᴹ grpdModel A B = {!!}
  -- Π[]ᴹ grpdModel A B σ x = {!!}
  Elᴹ grpdModel A = ConstFunctor _ _ {!!}
  -- El[]ᴹ grpdModel A σ x = {!!}
  -- lamᴹ grpdModel x = {!!}
  -- appᴹ grpdModel x = {!!}
  -- βᴹ grpdModel t x = {!!}
  -- ηᴹ grpdModel f x = {!!}
