{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}

module GroupoidModel.PiTypes {l} {l'} where

open import Utils
open import Function using (_$_)
open import Model
open import CategoryTheory
open import Data.Product
open import Cubical.Core.Prelude
open import GroupoidModel.Groupoid
open import GroupoidModel.Basics

open Functor
open Groupoid
open Category
open Tm
open import IdUtils

postulate
  swap-pathover : ∀{l l'} {A : Set l} (B : A -> Set l') {a b : A}
                -> (p : a ≡ b) (u : B a) (v : B b)
                -> subst B p u ≡ v -> u ≡ subst B (sym p) v

_◂ : ∀{Γ} {A : Ty {l} {l} Γ} → Tm Γ A → GrpdFunctor Γ (Γ ,, A)
_₀ (M ◂) γ = γ , (M ₀') γ
_₁ (M ◂) p = p , (M ₁') p
fid (_◂ {Γ} {A} M) x = ap (id (cat Γ) x ,_) goal'
  where
    D = λ z → Morph (cat ((A ₀) x)) z ((M ₀') x)
    p = cong (_$ ((M ₀') x)) (cong _₀ (fid A x))
    goal' = swap-pathover D p _ _ (fid' M x)
f∘ (_◂ {Γ} M) f g = ap ((cat Γ ∘ f) g ,_) {!!}

Tmᴳ : ∀{Γ} (A : Ty Γ) → Groupoid
cat (Tmᴳ {Γ} A) =
  record
    { Obj = Tm Γ A
    ; Morph = λ M N
      → Σ ((γ : Obj (cat Γ)) → Morph (cat ((A ₀) γ)) ((M ₀') γ) ((N ₀') γ)) λ τ
      → isNatural _ _ (M ◂) (N ◂) (λ γ → id (cat Γ) _ ,
          subst (λ z → Morph (cat ((A ₀) γ)) z ((N ₀') γ)) (sym (cong (_$ _) $ cong _₀ $ fid A γ)) (τ γ))
    ; id = λ M → (λ γ → id (cat ((A ₀) γ)) ((M ₀') γ)) , λ f → {!!}
    ; _∘_ = {!!}
    ; hom-set = {!!}
    ; id∘ = {!!}
    ; ∘id = {!!}
    ; ∘∘ = {!!}
    }
grpd (Tmᴳ A) = {!!}
strct (Tmᴳ A) = {!!}

module _ {Γ} (A : Ty {l}{l} Γ) (B : Ty (Γ ,, A)) where

  Π' : (γ : Obj (cat Γ)) → Ty ((A ₀) γ)
  _₀ (Π' γ) x = (B ₀) (γ , x)
  _₁ (Π'  γ) p =
    (B ₁) (id (cat Γ) γ ,
               subst (λ z → Morph (cat ((A ₀) γ)) z _)
                 (sym (cong (_$ _) (cong _₀ (fid A γ)))) p)
  fid (Π' γ) x =
    cong (B ₁) (Σ-≡ (refl , transpRefl (Morph (cat ((A ₀) γ)) _ _) _)) · fid B (γ , x)
  f∘ (Π' γ) f g = Functor-≡ {!!} {!!} {!!} {!!} {!!}

  auxM : ∀{γ γ'} (p : Morph (cat Γ) γ γ')
       -> Tm ((A ₀) γ) (Π' γ) -> Tm ((A ₀) γ') (Π' γ')
  _₀' (auxM {γ} {γ'} p M) a = (((B ₁) (p , id')) ₀) ((M ₀') (((A ₁) p⁻¹ ₀) a))
    where p⁻¹ = fst (grpd Γ p)
          C = cat ((A ₀) γ')
          id' = substMorph {C = C} (sym ((apF0 _ _ _ _ a $ ap (A ₁) $ snd (snd (grpd Γ p))) · apF0 _ _ _ _ a (fid A γ')) · ap (_$ a) (ap _₀ (f∘ A p p⁻¹))) (id C a)
  _₁' (auxM {γ} {γ'} p M) {a} {a'} q =
    substMorph {C = (cat ((B ₀) (γ' , a')))} goal aux'
    where
      p⁻¹ = fst (grpd Γ p)
      aux = (M ₁') ((((A ₁) p⁻¹) ₁) q)
      id' = g-id Γ A p a'
      aux' = (((B ₁) (p , id')) ₁) aux
      goal : ((B ₁) (p , id') ₀) ((((Π' γ) ₁) (((A ₁) p⁻¹ ₁) q) ₀) ((M ₀') (((A ₁) p⁻¹ ₀) a)))
           ≡ ((((Π' γ') ₁) q) ₀) (((B ₁) (p , _) ₀) ((M ₀') (((A ₁) p⁻¹ ₀) a)))
      goal = {!!}
  fid' (auxM {γ} {γ'} p M) = {!!}
  f∘' (auxM {γ} {γ'} p M) = {!!}

  auxM→ : ∀{γ γ'} (M M' : Tm ((A ₀) γ) (Π' γ))
        -> Morph (cat (Tmᴳ (Π' γ))) M M'
        -> (p : Morph (cat Γ) γ γ')
        -> Morph (cat (Tmᴳ (Π' γ'))) (auxM p M) (auxM p M')
  fst (auxM→ {γ} {γ'} M M' (τ , isNat) p) a =
    (((B ₁) (p , g-id Γ A p a)) ₁) (τ (fmp0 Γ A _ _ p⁻¹ a))
    where
      p⁻¹ = fst (grpd Γ p)
  snd (auxM→ M M' (τ , isNat) p) f = {!!}

  Π : Ty Γ
  _₀ Π γ = Tmᴳ {(A ₀) γ} (Π' γ)
  _₁ Π {γ} {γ'} p = F
    where
      F : GrpdFunctor (Tmᴳ (Π' _)) (Tmᴳ (Π' _))
      _₀ F = auxM p
      _₁ F {M} {M'} τ = auxM→ M M' τ p
      fid F = {!!}
      f∘ F = {!!}
  fid Π = {!!}
  f∘ Π = {!!}

  module _ (M : Tm (Γ ,, A) B) where

    lam₀ : (γ : Obj (cat Γ)) → Obj (cat ((Π ₀) γ))
    lam₀ γ =
      MkTm (λ x → (M ₀') (γ , x))
           (λ u → (M ₁') (id (cat Γ) γ , subst (λ z →
             Morph (cat ((A ₀) γ)) z _) (sym (cong (_$ _) $ cong _₀ (fid A γ))) u))
           {!!} {!!}

    lam₁ : ∀{γ γ'} → (p : Morph (cat Γ) γ γ')
         → Morph (cat $ (Π ₀) γ') (((Π ₁) p ₀) (lam₀ γ)) (lam₀ γ')
    lam₁ {γ} {γ'} p = τ , {!!}
      where
        τ : (x' : Obj $ cat $ (A ₀) γ')
          → Morph (cat $ (B ₀) (γ' , x'))
                  ((((((Π ₁) p) ₀) (lam₀ γ)) ₀') x')
                  (((lam₀ γ') ₀') x')
        τ x' = (M ₁') (p , g-id Γ A p x')

    lam : Tm Γ Π
    _₀'  lam = lam₀
    _₁'  lam = lam₁
    fid' lam = {!!}
    f∘'  lam = {!!}

  module _ (M : Tm Γ Π) where

    app : Tm (Γ ,, A) B
    _₀' app (γ , x) = (((M ₀') γ) ₀') x
    _₁' app {γ , x} {γ' , x'} (p , q) = _∘_ (cat ((B ₀) (γ' , x'))) aux aux''''
      where
        p⁻¹ = fst (grpd Γ p)
        q' : Morph (cat ((A ₀) γ')) (((A ₁) (id (cat Γ) γ') ₀) (fmp0 Γ A _ _ p x)) x'
        q' = substMorph {C = cat ((A ₀) γ')} (sym $ ap (_$ (fmp0 Γ A γ γ' p x)) $ ap _₀ (fid A γ')) q
        p· = fmp0 Γ A _ _ p
        p⁻¹· = fmp0 Γ A _ _ p⁻¹
        p·' = fmp0 Γ Π _ _ p
        p-id· = fmp0 (Γ ,, A) B _ _ (p , (id (cat (A ₀ $ γ')) (p· x)))
        id-q· = fmp0 (Γ ,, A) B _ _ (id (cat Γ) γ' , q')
        p-q· = fmp0 (Γ ,, A) B _ _ (p , q)
        p-id·' = fmp0 (Γ ,, A) B _ _ (p , g-id Γ A p (p· x))

        aux : Morph (cat $ (B ₀) (γ' , x'))
                    (id-q· ((((M ₀') γ') ₀') (p· x)))
                    (((M ₀') γ' ₀') x')
        aux = (((M ₀') γ') ₁') q

        aux' : Morph (cat ((B ₀) (γ' , p· x)))
                     (((p·' ((M ₀') γ)) ₀') (p· x))
                     (((M ₀') γ' ₀') (p· x))
        aux' = fst ((M ₁') p) (p· x)

        aux'' : Morph (cat ((B ₀) (γ' , p· x)))
                      (p-id· ((M ₀' $ γ) ₀' $ x))
                      ((((M ₀') γ' ₀') (p· x)))
        aux'' = substMorph {C = cat ((B ₀) (γ' , p· x))} goal aux'
          where
            goal : (p·' ((M ₀') γ) ₀') (p· x) ≡ p-id· ((((M ₀') $ γ) ₀') $ x)
            goal = begin
               p-id·' ((M ₀' $ γ) ₀' $ p⁻¹· (p· x))
                 ≡⟨ {!!} ⟩
               p-id· ((M ₀' $ γ) ₀' $ x)
                 ∎

        aux''' : Morph (cat $ (B ₀) (γ' , x'))
                       (id-q· (p-id· ((M ₀' $ γ) ₀' $ x)))
                       (id-q· ((M ₀' $ γ') ₀' $ p· x))
        aux''' = (B ₁ $ (id (cat Γ) γ') , q') ₁ $ aux''

        aux'''' : Morph (cat $ (B ₀) (γ' , x'))
                        (p-q· ((M ₀' $ γ) ₀' $ x))
                        (id-q· ((M ₀' $ γ') ₀' $ p· x))
        aux'''' = substMorph {C = cat $ (B ₀) (γ' , x')} {!!} aux'''
          where
            fmpAB = fmp0 (Γ ,, A) B
            goal : id-q· (p-id· ((((M ₀') $ γ) ₀') $ x)) ≡ p-q· ((((M ₀') $ γ) ₀') $ x)
            goal = begin
              fmpAB _ _ (id (cat Γ) γ' , q') (fmpAB _ _ (p , id (cat (A ₀ $ γ')) (p· x)) ((((M ₀') $ γ) ₀') $ x))
                ≡⟨ fmp0∘ (Γ ,, A) B (p , (id (cat (A ₀ $ γ')) (p· x))) (id (cat Γ) γ' , q') ((((M ₀') $ γ) ₀') $ x) ⟩
              fmpAB _ _ (_∘_ (cat (Γ ,, A)) (id (cat Γ) γ' , q') (p , (id (cat (A ₀ $ γ')) (p· x)))) ((((M ₀') $ γ) ₀') $ x)
                ≡⟨ {!!} ⟩
              {!!}
    fid' app = {!!}
    f∘' app = {!!}
