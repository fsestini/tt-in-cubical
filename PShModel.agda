{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --prop #-}
{-# OPTIONS --cubical #-}

module PShModel where

open import Utils
open import Function using (_$_)
open import Cubical.Core.Prelude
open import Model
open import Data.Unit
open import Data.Product
open import CategoryTheory
open import IrrelevantProp
open import Agda.Primitive

open Model.Model

-- co-foo : ∀{l}{A : Set l} {B : A → Set l} → (p q : Σ A B)
--     → p ≡ q
--     → Σ (proj₁ p ≡ proj₁ q) (λ r → subst B r (proj₂ p) ≡ proj₂ q)
-- co-foo p q r = cong fst r , fromPathP (cong snd r)

module _ {l l'} (C : Category {l} {l'}) where

  open Functor
  open Σ'

  PShC = PSh {l'' = l ⊔ l'} C

  PShTy : PShCon → Set _
  PShTy Γ = PSh {l'' = l ⊔ l'} (∫ C Γ)

  PShTms : PShCon → PShCon → Set _
  PShTms Δ Γ = NatTrans _ _ Δ Γ

  psh-swap : {Γ : PShCon} {A : PShTy Γ}
           → ∀{I J} (u : Category.Morph C J I)
           → (γ : _) (γ' : _) (γ'' : _)
           → (p : ∥ (Γ ₁) u γ ≡ γ' ∥) → (q : γ' ≡ γ'')
           → (x : (A ₀) (I , γ))
           → subst (λ x → (A ₀) (J , x)) q ((A ₁) (u , p) x) ≡ (A ₁) (u , p ● ∣ q ∣) x
  psh-swap u γ γ' γ'' p q x = {!!}

  pshModel : Model
  Conᴹ pshModel = PShCon
  Tyᴹ  pshModel = PShTy
  Tmsᴹ pshModel = λ Δ Γ → NatTrans _ _ Δ Γ
  Tmᴹ  pshModel =
    λ Γ A → Σ' ((I : Obj C) → (γ : (Γ ₀) I) → (A ₀) (I , γ)) λ M
                        → ∀{I J} → (γ : (Γ ₀) I) → (u : Morph C J I) -- → (p : ∥ (Γ ₁) u γ ≡ (Γ ₁) u γ ∥)
                          → ∥ (A ₁) (u , ∣ refl ∣) (M I γ) ≡ M J ((Γ ₁) u γ) ∥
    where open Category.Category

  ◇ᴹ pshModel = HasTerminalObj.one (PShTerm C)
  _,ᴹ_ pshModel Γ A =
    record { _₀ = λ c → Σ ((Γ ₀) c) λ γ → (A ₀) (c , γ)
           ; _₁ = λ { u (γ , x) → ((Γ ₁) u γ) , ((A ₁) (u , ∣ refl ∣) x) }
           ; fid = do
               fΓ <- fid Γ
               fA <- fid A
               ∣ (λ I → funExt _ λ { (γ , x) →
                   Σ-≡ (cong (_$ γ) (fΓ I) ,
                     psh-swap {Γ} {A} (Category.id C I) γ _ γ
                       ∣ refl ∣ (cong (_$ γ) (fΓ I)) x
                         · cong (_$ x) (fA (I , γ)) )}) ∣
           ; f∘ = {!!}
           }

  _[_]ᴹ pshModel {Θ} {Γ} A σ = uhm A σ
  idᴹ pshModel = λ Γ →  IdNatTrans _ _ {Γ}
  εᴹ pshModel {Γ} = HasTerminalObj.bang (PShTerm C) Γ
  _∘ᴹ_ pshModel σ τ = σ ∘ τ
    where open Category.Category (PShCat {l'' = l ⊔ l'} C)
  π₁ᴹ pshModel σ = (λ c x → fst (fst' σ c x)) , λ f → congTr (λ f x → fst (f x)) (snd' σ f)
  π₂ᴹ pshModel {Γᴹ = Γ} {Δ} {A} σ = M , λ γ u → {!!}
    where
      open Category.Category
      M : _
      M I γ = snd (fst' σ I γ)
      --   where
      --     aux = congTr (_$ γ) (snd' σ u)
  _,sᴹ_ pshModel σ t = (λ I γ → fst' σ I γ , fst' t I γ) , λ f → do
    ke <- snd' σ f
    ∣ funExt _ (λ x → Σ-≡ (cong (_$ x) ke , {!!})) ∣ -- psh-swap f {!!} {!!} {!!} {!!} {!!} (fst' t _ x) · {!!})) ∣
  _[_]'ᴹ pshModel {Γᴹ = Γ} {Δᴹ = Δ} {Aᴹ = A} (M , h) σ = M[σ] , {!!}
    where
      M[σ] : _
      M[σ] I γ = M I (fst' σ I γ)

  _[_]'∘ᴹ pshModel t σ = {!!}

  [id]ᴹ pshModel {Γᴹ = Γ} A =
    Functor-≡ _ _ (uhm A idtr) A
    (λ _ → refl) λ { {a = (I , γ)} {(J , γ')} (u , p) →
      transpRefl _ (subst (λ B → (A ₀) (I , fst' idtr I γ) → B)
       (λ _ → (A ₀) (J , fst' idtr J γ'))
       (λ x → (A ₁) (u , _) x)) ·
         transpRefl _ (λ x →
           (A ₁) (u , _) x) · funExt _ (λ _ → refl)
           }
    where idtr = (IdNatTrans (C ᵒᵖ) Sets {Γ})

  [][]ᴹ pshModel = {!!}
  ∘∘ᴹ pshModel = {!!}
  id∘ᴹ pshModel = {!!}
  ∘idᴹ pshModel = {!!}
  εηᴹ pshModel  = {!!}
  [][]∘ᴹ pshModel = {!!}
  π₁βᴹ pshModel = {!!}
  π₂βᴹ pshModel = {!!}
  πηᴹ pshModel  = {!!}
  ,∘₁ᴹ pshModel = {!!}
  ,∘₂ᴹ pshModel = {!!}

  π₂∘ᴹ pshModel σ = {!!}
  π₂≡ᴹ pshModel σ i = {!!}
  Uᴹ pshModel = {!!}
  U[]ᴹ pshModel σᴹ x = {!!}
  _[_]'Uᴹ pshModel x σ = {!!}
  []U≡ᴹ pshModel t σ i = {!!}
  Πᴹ pshModel {Γ} A B =
    MkFunct (λ { (I , γ) → ∀{J} (w : Morph J I) (x : (A ₀) (J , (Γ ₁) w γ))
                           → (B ₀) (J , ((Γ ₁) w γ , x))})
            (λ { (u , p) f {J} w x →
              let aux = f {J} (u ∘ w) (subst (λ x → (A ₀) (J , x)) {!!} x)
              in subst (λ x → (B ₀) (J , x)) (Σ-≡ ({!!} , {!!})) aux })
                 {!!} {!!}
    where open Category.Category C
  Π[]ᴹ pshModel A B σ = {!!}
  Elᴹ pshModel A = {!!}
  El[]ᴹ pshModel A σ x = {!!}
  lamᴹ pshModel x = {!!}
  appᴹ pshModel x = {!!}
  βᴹ pshModel t x = {!!}
  ηᴹ pshModel f x = {!!}
