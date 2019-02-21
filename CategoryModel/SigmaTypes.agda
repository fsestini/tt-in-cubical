module CategoryModel.SigmaTypes {l} where

open import Function using (_$_)
open import Cubical.Core.Prelude
open import CategoryTheory
open import Utils
open import Agda.Primitive
open import CategoryModel.MorphUtils
open import CategoryModel.Basics {l}

open TyUtils strct

module _ {Γ : Category} (A : Ty Γ) (B : Ty (Γ ,, A)) where

  open Functor
  open Category

  module _ (γ : Obj Γ) where
    B' : Ty ((A ₀) γ)
    (B' ₀) x = (B ₀) (γ , x)
    (B' ₁) f = (B ₁) (id Γ γ , overFidL A f)
    fid B' = {!!}
    f∘ B' = {!!}

  module _ {γ γ' : Obj Γ} (p : Morph Γ γ γ') where

    aux : ((A ₀) γ ,, B' γ) ⟶ ((A ₀) γ' ,, B' γ')
    (aux ₀) (a , b) = ((A ₁) p ₀) a , ((B ₁) (p , id ((A ₀) γ') _) ₀) b
    (aux ₁) {a , b} {a' , b'} (f , g) =
      ((A ₁) p ₁) f , MU.substMorph ((B ₀) (γ' , p·a'))
        (asder B _ _ _ _ b {!!}) g'
      where
        p·a = ((A ₁) p ₀) a
        p·a' = ((A ₁) p ₀) a'
        g' = ((B ₁) (p , id ((A ₀) γ') _) ₁) g

    fid aux = {!!}
    f∘  aux = {!!}

  Σ-ty : Ty Γ
  (Σ-ty ₀) γ = (A ₀) γ ,, (B' γ)
  (Σ-ty ₁) f = aux f
  fid Σ-ty γ = {!!}
  f∘  Σ-ty = {!!}


module _ {Γ : Category} (A : Ty Γ) (B : Ty (Γ ,, ty-op A)) where

  open Functor
  open Category

  module _ (γ : Obj Γ) where

    Bop' : Ty (((A ₀) γ) ᵒᵖ)
    (Bop' ₀) x = (B ₀) (γ , x)
    (Bop' ₁) f = (B ₁) (id Γ γ , overFidR A f)
    fid Bop' = {!!}
    f∘ Bop' = {!!}

  module _ {γ γ' : Obj Γ} (p : Morph Γ γ γ') where

    auxop : ((A ₀) γ ,,op Bop' γ) ⟶ ((A ₀) γ' ,,op Bop' γ')
    (auxop ₀) (a , b) = ((A ₁) p ₀) a , ((B ₁) (p , id ((A ₀) γ') _) ₀) b
    (auxop ₁) {a , b} {a' , b'} (f , g) =
      ((A ₁) p ₁) f , MU.substMorphR ((B ₀) (γ' , p·a)) {!!} g'
      where
        p·a = ((A ₁) p ₀) a
        p·a' = ((A ₁) p ₀) a'
        g' = ((B ₁) (p , id ((A ₀) γ') _) ₁) g
    fid auxop = {!!}
    f∘ auxop = {!!}
    
  Σop-ty : Ty Γ
  (Σop-ty ₀) γ = (A ₀) γ ,,op Bop' γ 
  (Σop-ty ₁) p = auxop p
  fid Σop-ty = {!!}
  f∘  Σop-ty = {!!}
