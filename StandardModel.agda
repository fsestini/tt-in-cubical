module StandardModel where

open import Function
open import Cubical.Core.Prelude
open import Model
open import Data.Unit
open import Data.Product

foo : {A : Set} {B : A → Set} → (p q : Σ A B)
    → Σ (proj₁ p ≡ proj₁ q) (λ r → subst B r (proj₂ p) ≡ proj₂ q)
    → p ≡ q
foo {A} {B} p@(p1 , p2) q@(q1 , q2) (h1 , h2) =
  compPath (J (λ q1' k' → (p1 , p2) ≡ (q1' , subst B k' p2))
              (cong (λ x → p1 , x) (sym (substRefl B p2))) h1)
           (cong (λ x → (q1 , x)) h2)

StdConᴹ = Set

StdTyᴹ : StdConᴹ → Set₁
StdTyᴹ = λ Γ → Γ → Set

StdTmsᴹ : StdConᴹ → StdConᴹ → Set
StdTmsᴹ = λ Γᴹ Δᴹ → Γᴹ → Δᴹ

StdTmᴹ : (Γᴹ : StdConᴹ) → StdTyᴹ Γᴹ → Set
StdTmᴹ = λ Γᴹ Aᴹ → (ρ : Γᴹ) → Aᴹ ρ

open Model.Model

stdModel : Model
Conᴹ stdModel = StdConᴹ
Tyᴹ  stdModel = StdTyᴹ
Tmsᴹ stdModel = StdTmsᴹ
Tmᴹ  stdModel = StdTmᴹ

◇ᴹ stdModel = ⊤
_,ᴹ_ stdModel = λ Γᴹ Aᴹ → Σ Γᴹ Aᴹ
_[_]ᴹ stdModel = λ Aᴹ σᴹ x → Aᴹ (σᴹ x)
idᴹ stdModel Γᴹ x = x
εᴹ stdModel _ = tt
_∘ᴹ_ stdModel = λ z z₁ z₂ → z (z₁ z₂)
π₁ᴹ stdModel x y = proj₁ (x y)
π₂ᴹ stdModel σᴹ ρ = proj₂ (σᴹ ρ)
_,sᴹ_ stdModel = λ σᴹ x y → σᴹ y , x y
_[_]'ᴹ stdModel = λ tᴹ σᴹ ρ → tᴹ (σᴹ ρ)
_[_]'∘ᴹ stdModel = λ tᴹ σᴹ ρ → tᴹ (σᴹ ρ)

[id]ᴹ stdModel _ = refl
[][]ᴹ stdModel = refl
∘∘ᴹ stdModel = refl
id∘ᴹ stdModel = refl
∘idᴹ stdModel = refl
εηᴹ stdModel = refl
[][]∘ᴹ stdModel _ _ = refl
π₁βᴹ stdModel = refl
π₂βᴹ stdModel = refl
πηᴹ stdModel = refl
,∘₁ᴹ stdModel = refl
,∘₂ᴹ stdModel = refl
