module GroupoidModel.Model {l} where

open import GroupoidModel.Groupoid
open import GroupoidModel.Basics
open import Utils
open import GroupoidModel.PiTypes
open import GroupoidModel.IdTypes
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
π₁ᴹ  grpdModel {Γᴹ = Γ} σ = π₁ Γ σ
_[_]ᴹ grpdModel A f = compFun f A
_[_]'ᴹ grpdModel = _[_]'
_,sᴹ_ grpdModel = _,s_
π₂ᴹ  grpdModel {Γᴹ = Δ} {Γ} {Aᴹ = A} σ = π₂ σ
◇ᴹ grpdModel =
  record { cat = ⊤-cat ; strct = λ _ _ → refl ; grpd = λ f → tt , refl , refl }
idᴹ grpdModel Γᴹ = IdFunctor (cat Γᴹ)
εᴹ grpdModel = MkFunct (λ _ → tt) (λ _ → tt) (λ _ → refl) λ _ _ → refl
εηᴹ grpdModel =
  Functor-≡' _ _ _ _
    (record { eq0 = λ _ → refl ; eq1 = λ f → transpRefl _ _ · transpRefl _ _ })
_∘ᴹ_ grpdModel F G = compFun G F
[id]ᴹ grpdModel Aᴹ = Functor-≡' _ _ _ _ (FunctorEq-refl _ _ Aᴹ)
[][]ᴹ grpdModel {σᴹ = σ} {τ} {A} = Functor-≡' _ _ _ _ (FunctorEq-refl _ _ (compFun τ (compFun σ A)))
id∘ᴹ grpdModel {σᴹ = σ} = Functor-≡' _ _ _ _ (FunctorEq-refl _ _ σ)
∘idᴹ grpdModel {σᴹ = σ} = Functor-≡' _ _ _ _ (FunctorEq-refl _ _ σ)
∘∘ᴹ grpdModel {σᴹ = σ} {τ} {δ} = Functor-≡' _ _ _ _ (FunctorEq-refl _ _ (compFun δ (compFun τ σ)))
π₁βᴹ grpdModel = Functor-≡' _ _ _ _ (record { eq0 = λ x → refl ; eq1 = λ f → transpRefl _ _ · transpRefl _ _ })
π₂βᴹ grpdModel = {!!}
πηᴹ grpdModel = {!!}
,∘₁ᴹ grpdModel = {!!}
,∘₂ᴹ grpdModel = {!!}
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
Idᴹ grpdModel {Γ = Γ} A = IdType Γ A
-- lam[]ᴹ grpdModel t σ = {!!}
-- ty-trunc grpdModel = {!!}
