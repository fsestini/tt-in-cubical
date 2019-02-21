module StandardModel where

open import Function
open import Cubical.Core.Prelude
open import Model
open import Data.Product
open import GeneralizedModel


open import Utils
open import Relation.Nullary
open import IR-Universes
open import Data.Unit

postulate
  dec𝓤₁ : (x y : 𝓤₁) -> Dec (x ≡ y)
  hedberg : ∀{l} {A : Set l} -> ((x y : A) -> Dec (x ≡ y)) -> isSet A

open GeneralizedModel.GeneralizedModel

stdM : GeneralizedModel
ConUniv stdM = 𝓤₂
ConEl stdM = El₂
TyUniv stdM = 𝓤₂
TyEl stdM = El₂
TmsUniv stdM = 𝓤₁
TmsEl stdM = El₁
TmUniv stdM = 𝓤₁
TmEl stdM = El₁
Conᴹ stdM = 𝓤₁-code
Tyᴹ stdM = λ Γ → 𝓤₂-Π Γ (λ _ → 𝓤₁-code)
Tmsᴹ stdM = λ Γ Δ → 𝓤₁-Π Γ λ _ → Δ
Tmᴹ stdM = λ Γ A → 𝓤₁-Π Γ (λ ρ → A ρ)
◇ᴹ stdM = 𝓤₁-⊤
_,ᴹ_ stdM = λ Γ A → 𝓤₁-Σ Γ A
Πᴹ stdM = λ A B γ → 𝓤₁-Π (A γ) λ a → B (γ , a)
Uᴹ stdM = λ _ → 𝓤-code
Elᴹ stdM = λ A a → cumul (A a)
_[_]ᴹ stdM A σ γ = A (σ γ)
idᴹ stdM Γᴹ γ = γ
εᴹ stdM _ = tt
εηᴹ stdM = refl
_∘ᴹ_ stdM σ τ γ = σ (τ γ)
[id]ᴹ stdM Aᴹ = refl
[][]ᴹ stdM = refl
id∘ᴹ stdM = refl
∘idᴹ stdM = refl
∘∘ᴹ stdM = refl
_,sᴹ_ stdM σ t γ = σ γ , t γ
π₁ᴹ stdM σ γ = fst (σ γ)
π₂ᴹ stdM σ γ = snd (σ γ)
π₁βᴹ stdM = refl
π₂βᴹ stdM = refl
πηᴹ stdM = refl
_[_]'ᴹ stdM t σ γ = t (σ γ)
,∘₁ᴹ stdM = refl
,∘₂ᴹ stdM = {!!}
U[]ᴹ stdM σᴹ = refl
Π[]ᴹ stdM A B σ = funExt _ (λ δ → ap (𝓤₁-Π (A (σ δ))) (funExt _ (λ a → ap B (Σ-≡ (refl , {!!})))))
El[]ᴹ stdM A σ = funExt _ λ x → ap (λ x → cumul (A (σ x))) (sym (transpRefl _ x))
lamᴹ stdM t γ a = t (γ , a)
appᴹ stdM t (γ , a) = t γ a
βᴹ stdM t = refl
ηᴹ stdM f = refl
lam[]ᴹ stdM t σ = {!!}
Idᴹ stdM A ((γ , a) , a') = 𝓤₁-Id (A γ) a a'
ty-trunc stdM = Π-set λ _ → hedberg dec𝓤₁
