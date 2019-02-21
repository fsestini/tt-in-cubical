module CategoryModel.PiTypes {l} where

open import Function using (_$_)
open import Cubical.Core.Prelude
open import CategoryTheory
open import Utils
open import Agda.Primitive
open import CategoryModel.MorphUtils
open import CategoryModel.Basics {l}

open TyUtils strct

module _ {Γ : Category} (A : Ty (Γ ᵒᵖ)) (B : Ty (Γ ,,op A)) where

  open Functor
  open Tm
  open Category

  private
    Π' : (γ : Obj Γ) -> Ty ((A ₀) γ)
    (Π' γ ₀) x = (B ₀) (γ , x)
    (Π' γ ₁) {a = a} {b} p = (B ₁) (id Γ _ , overFidR A p)
    fid (Π' γ) x = fid B (γ , x)
    f∘ (Π' γ) f g =
      ap (B ₁) (Σ-≡ (sym (id∘ Γ _) , goal)) ·
        f∘ B (id Γ γ , overFidR A f) (id Γ γ , overFidR A g)
      where
        open MU ((A ₀) γ)
        goal = begin
          _ ≡⟨ joinSMR-2 _ _ _ ⟩
          _ ≡⟨ substMorphR-irrel _ (strct ((A ₀) γ) _ _) ⟩
          _ ≡⟨ sym (joinSMR-3 _ _ _ _) ⟩
          _ ≡⟨ ap (overF∘R A _ _) (ap (substMorphR _)
                  (sym $ substMorphR∘ (overFid-prf A _) g f)) ⟩
          _ ≡⟨ ap (overF∘R A _ _) (sym (substMorph2∘' _ _ _ _)) ⟩
          _ ≡⟨ ap (overF∘R A _ _) (ap (λ z → _∘_ ((A ₀) γ) z (overFidR A g))
                           (sym $ IdFun-lemma A (overFidR A f))) ⟩
          _ ≡⟨ sym (overF∘R-comp A _ _ _ _) ⟩
          _ ∎

    Π'-fun : ∀{γ γ'} -> Morph Γ γ γ'
           -> Tmᶜ ((A ₀) γ) (Π' γ) ⟶ Tmᶜ ((A ₀) γ') (Π' γ')
    ((Π'-fun p ₀) M ₀') a =
      (((B ₁) (p , idA)) ₀) ((M ₀') ((((A ₁) p) ₀) a))
      where idA = id ((A ₀) _) _
    ((Π'-fun {γ} {γ'} p ₀) M ₁') {a} {a'} q =
      MU.substMorph ((B ₀) (γ' , a')) prf aux
      where
        p·a' = ((A ₁) p ₀) a' ; p·q = ((((A ₁) p) ₁) q)
        aux = (((B ₁) (p , (id ((A ₀) γ) p·a'))) ₁) ((M ₁') p·q)
        prf = asder B _ _ _ _ _
                (p-id-q-lemma {Γ} A p q · sym (p-id-q-lemma' {Γ} A p q))
    fid' ((Π'-fun {γ} {γ'} p ₀) M) a = {!!}
    f∘' ((Π'-fun {γ} {γ'} p ₀) M) = {!!}
    fst ((Π'-fun {γ} {γ'} p ₁) (τ , _)) a =
      ((B ₁) (p , id ((A ₀) γ) _) ₁) (τ (((A ₁) p ₀) a))
    snd ((Π'-fun {γ} {γ'} p ₁) (τ , nat-τ)) = {!!}
    fid (Π'-fun {γ} {γ'} p) x =
      Σ-≡ (funExt _ (λ a → fid ((B ₁) (p , id ((A ₀) γ) _)) _) ,
        {!!})
    f∘ (Π'-fun {γ} {γ'} p) = {!!}

  Π : Ty Γ
  (Π ₀) γ = Tmᶜ ((A ₀) γ) (Π' γ)
  (Π ₁) {γ} {γ'} p = Π'-fun p
  fid Π x = {!!}
  f∘ Π = {!!}

module _ {Γ : Category} (A : Ty (Γ ᵒᵖ)) (B : Ty (Γ ,,op ty-op A)) where

  open Functor
  open Category
  open Tm

  Πᵒᵖ' : (γ : Obj Γ) -> Ty (((ty-op A) ₀) γ)
  (Πᵒᵖ' γ ₀) x = (B ₀) (γ , x)
  (Πᵒᵖ' γ ₁) {a = a} {b} p = (B ₁) (id Γ _ , overFidL A p)
  fid (Πᵒᵖ' γ) a = {!!}
  f∘  (Πᵒᵖ' γ) = {!!}
  
  Πᵒᵖ'-fun : ∀{γ γ'} -> Morph Γ γ γ'
           -> Tmᶜ (((ty-op A) ₀) γ) (Πᵒᵖ' γ) ⟶ Tmᶜ (((ty-op A) ₀) γ') (Πᵒᵖ' γ')
  (((Πᵒᵖ'-fun {γ} {γ'} p ₀) M) ₀') a =
    (((B ₁) (p , id ((A ₀) γ) _)) ₀) ((M ₀') ((((A ₁) p) ₀) a))
  (Πᵒᵖ'-fun p ₁) = {!!}

  Πᵒᵖ : Ty Γ
  (Πᵒᵖ ₀) γ = Tmᶜ (((ty-op A) ₀) γ) (Πᵒᵖ' γ)
  (Πᵒᵖ ₁) p = Πᵒᵖ'-fun p
  fid Πᵒᵖ = {!!}
  f∘  Πᵒᵖ = {!!}
