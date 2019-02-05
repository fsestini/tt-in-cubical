module GroupoidModel.Model {l} where

open import GroupoidModel.Groupoid
open import GroupoidModel.Basics
open import Utils
open import GroupoidModel.PiTypes
open import Model
open import CategoryTheory
open import Cubical.Core.Prelude
open import Agda.Primitive

open Model.Model
open Groupoid
open import GroupoidModel.Universe {l}

Con = Groupoid {lsuc l}
Tms = GrpdFunctor {lsuc l} {lsuc l}

grpdModel : Model {lsuc (lsuc l)} {lsuc (lsuc l)} {lsuc l} {lsuc l}
Conᴹ grpdModel = Groupoid {lsuc l}
Tmsᴹ grpdModel = GrpdFunctor {lsuc l} {lsuc l}
Tyᴹ grpdModel Γ = cat Γ ⟶ Grpd {lsuc l}
Tmᴹ grpdModel Γ A = Tm Γ A
_,ᴹ_ grpdModel Γ A = Γ ,, A

  -- grpdModel : Model
  -- Conᴹ grpdModel = Groupoid {lsuc l}
  -- Tmsᴹ grpdModel = GrpdFunctor
  -- Tyᴹ  grpdModel Γ = cat Γ ⟶ Grpd {lsuc l}
  -- Tmᴹ  grpdModel Γ A = Tm Γ A
  -- -- π₁ᴹ  grpdModel {Γᴹ = record { cat = Γ }} σ =
  -- --   MkFunct (λ x → fst ((σ ₀) x))
  -- --           (λ f → fst ((σ ₁) f))
  -- --           (λ x → cong fst (fid σ x))
  -- --           λ f g → cong fst (f∘ σ f g)
  -- --   where open Functor
_[_]ᴹ grpdModel A f = compFun f A
  -- -- _[_]'ᴹ grpdModel = _[_]'
  -- -- _,sᴹ_ grpdModel {Γᴹ = record { cat = Δ }} {record { cat = Γ }} f M =
  -- --   MkFunct (λ δ → (f ₀) δ , (M ₀') δ)
  -- --           (λ u → (f ₁) u , (M ₁') u)
  -- --           (λ x → {!!}) {!!}
  -- --   where open Category ; open Functor ; open Tm
  -- -- π₂ᴹ  grpdModel {Γᴹ = Δ} {Γ} {Aᴹ = A} σ = π₂ σ

-- ◇ᴹ grpdModel = {!!}
idᴹ grpdModel Γᴹ = IdFunctor (cat Γᴹ)
-- εᴹ grpdModel = {!!}
  -- -- εηᴹ grpdModel x = {!!}
_∘ᴹ_ grpdModel F G = compFun G F
[id]ᴹ grpdModel Aᴹ = Functor-≡' _ _ _ _ (FunctorEq-refl _ _ Aᴹ)
[][]ᴹ grpdModel {σᴹ = σ} {τ} {A} = Functor-≡' _ _ _ _ (FunctorEq-refl _ _ (compFun τ (compFun σ A)))
id∘ᴹ grpdModel {σᴹ = σ} = Functor-≡' _ _ _ _ (FunctorEq-refl _ _ σ)
∘idᴹ grpdModel {σᴹ = σ} = Functor-≡' _ _ _ _ (FunctorEq-refl _ _ σ)
∘∘ᴹ grpdModel {σᴹ = σ} {τ} {δ} = Functor-≡' _ _ _ _ (FunctorEq-refl _ _ (compFun δ (compFun τ σ)))
  -- -- π₁βᴹ grpdModel x = {!!}
  -- -- π₂βᴹ grpdModel i = {!!}
  -- -- πηᴹ grpdModel x = {!!}
  -- -- ,∘₁ᴹ grpdModel x = {!!}
  -- -- _[_]'∘ᴹ grpdModel x σᴹ = {!!}
  -- -- ,∘₂ᴹ grpdModel i = {!!}
Uᴹ grpdModel = ConstFunctor _ _ Gpd
U[]ᴹ grpdModel σ = Functor-≡' _ _ _ _
  (record { eq0 = λ _ → refl ; eq1 = λ f → transpRefl _ _ · transpRefl _ _ })
Πᴹ grpdModel A B = Π A B
Π[]ᴹ grpdModel A B σ = {!!}
Elᴹ grpdModel A = El A
El[]ᴹ grpdModel A σ = {!!}
lamᴹ grpdModel t = lam _ _ t
appᴹ grpdModel t = app _ _ t
βᴹ grpdModel t = {!!}
ηᴹ grpdModel f = {!!}
