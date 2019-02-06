{-# OPTIONS --allow-unsolved-metas #-}

module GroupoidModel.Basics where

open import Utils
open import Function using (_$_)
open import CategoryTheory
open import Data.Product
open import Cubical.Core.Prelude
open import Agda.Primitive using (_⊔_)

open import GroupoidModel.Groupoid
open Groupoid

module _ {l} where

  Ty : (Γ : Groupoid {l}) → Set _
  Ty Γ = cat Γ ⟶ Grpd {l}

  module _ (Γ : Groupoid) (A : Ty Γ) where

    open Category
    open Functor

    fmp0 : ∀ γ γ' → GMorph Γ γ γ'
        → Obj (cat ((A ₀) γ)) → GObj ((A ₀) γ')
    fmp0 _ _ p = ((A ₁) p) ₀

    fmp0-id : ∀{γ} (x : _) → fmp0 _ _ (gid Γ γ) x ≡ x
    fmp0-id {γ} x = cong (_$ x) ((cong (_₀) (fid A γ)))

    fmp : ∀ {γ γ'} → GMorph Γ γ γ' → GrpdFunctor ((A ₀) γ) ((A ₀) γ')
    fmp p = ((A ₁) p)

    fmp0∘ : ∀{γ γ' γ''} (p : GMorph Γ γ γ') (q : GMorph Γ γ' γ'') (x : GObj ((A ₀) γ))
         -> fmp0 _ _ q (fmp0 _ _ p x) ≡ fmp0 _ _ (_∘_ (cat Γ) q p) x
    fmp0∘ p q x = sym $ ap (_$ x) $ ap _₀ $ f∘ A q p
      where open Category (cat Γ)
      
  record Tm (Γ : Groupoid) (A : Ty Γ) : Set l where
    no-eta-equality
    constructor MkTm
    open Category
    open Functor

    field
      _₀' : (γ : Obj (cat Γ)) → Obj (cat ((A ₀) γ))
      _₁' : ∀{γ γ'} → (p : GMorph Γ γ γ')
                    → GMorph ((A ₀) γ') (fmp0 Γ A γ γ' p (_₀' γ)) (_₀' γ')
      fid' : ∀ γ → let one = (_₁' (gid Γ γ))
                       two = gid ((A ₀) γ) (_₀' γ)
                   in subst (λ x → GMorph ((A ₀) γ) x (γ ₀')) (fmp0-id Γ A (γ ₀')) one ≡ two
      f∘'  : ∀{γ γ' γ''} → (p : GMorph Γ γ γ') (p' : GMorph Γ γ' γ'')
           → let one = _₁' (_∘_ (cat Γ) p' p)
                 two = _∘_ (cat ((A ₀) γ'')) (_₁' p') (((fmp Γ A p') ₁) (_₁' p))
             in subst (λ x → GMorph ((A ₀) γ'') x (γ'' ₀')) (cong (_$ γ ₀') (cong _₀ (f∘ A p' p))) one ≡ two

module _ {l} where

  _,,_ : (Γ : Groupoid {l}) → Ty {l} Γ → Groupoid {l}
  cat (g@(record { cat = Γ}) ,, A) = record
                   { Obj = Σ (Obj Γ) λ γ → Obj (cat ((A ₀) γ))
                   ; Morph = λ { (γ , x) (γ' , x') → Σ (Morph Γ γ γ') λ p → Morph (cat ((A ₀) γ')) (fmp0 g A _ _ p x) x' }
                   ; id = λ { (γ , x) → id Γ γ , substMorph {C = cat ((A ₀) γ)} (sym (cong (_$ x) (cong _₀ (fid A γ)))) (id (cat ((A ₀) γ)) x) }
                   ; _∘_ = λ { {γ , x} {γ' , x'} {γ'' , x''} (p' , q') (p , q)
                         → _∘_ Γ p' p , _∘_ (cat ((A ₀) γ'')) q' (substMorph {C = (cat ((A ₀) γ''))}
                                                     (sym (ap (_$ x) $ ap _₀ $ f∘ A p' p))
                                                     ((((A ₁) p') ₁) q)) }
                   ; hom-set = {!!}
                   ; id∘ = λ { (p , q) → Σ-≡ (id∘ Γ p , {!!}) }
                   ; ∘id = {!!}
                   ; ∘∘ = {!!}
                   }
    where open Category ; open Functor
  grpd (Γ ,, A) f = {!!}
  strct (Γ ,, A) = {!!}

-- module _ {l} {Γ : Groupoid {l}} {A : Ty {l} Γ} where

--   open Functor

  -- p : cat (Γ ,, A) ⟶ cat Γ
  -- (p ₀) (γ , x) = γ
  -- (p ₁) (p , q) = p
  -- fid p = {!!}
  -- f∘ p = {!!}

module _ {l} (Γ : Groupoid {l}) {Δ : Groupoid {l}} {A : Ty {l} Δ} where

  π₁ : cat Γ ⟶ cat (Δ ,, A) → cat Γ ⟶ cat Δ
  π₁ σ =
    MkFunct (λ x → fst ((σ ₀) x))
            (λ f → fst ((σ ₁) f))
            (λ x → cong fst (fid σ x))
            (λ f g → cong fst (f∘ σ f g))
    where open Functor ; open Category

--   module _ (Γ : Groupoid {l}) (A : Ty {l} {l'} Γ) (a : Tm Γ A) where

--     open Functor
--     open Tm

--     ,,fun : GrpdFunctor Γ (Γ ,, A)
--     (,,fun ₀) γ = γ , (a ₀' $ γ)
--     (,,fun ₁) p = p , (a ₁' $ p)
--     fid ,,fun γ = {!!}
--     f∘ ,,fun p q = {!!}

-- module _ {l} (H : (A : Groupoid {l}) -> Functor (cat (gcross A A)) (Grpd {l})) (Γ : Groupoid {l}) (A : Ty {l} {l} Γ) where

--     open Functor
--     open Category

--     asd : Functor (cat ((Γ ,, A) ,, compFun _ _ _ (p {l} {l} {Γ} {A}) A)) (Grpd {l})
--     (asd ₀) ((γ , x) , y) = (H ((A ₀) γ)) ₀ $ x , y
--     (asd ₁) = {!!}
--     fid asd = {!!}
--     f∘ asd = {!!}

--   -- π₁ : ∀{Γ Δ} {A : Ty Δ} → Γ ⟶ cat (Δ ,, A) → Γ ⟶ cat Δ
--   -- π₁ σ =
--   --   MkFunct (λ x → fst ((σ ₀) x))
--   --           (λ f → fst ((σ ₁) f))
--   --           (λ x → cong fst (fid σ x))
--   --           λ f g → cong fst (f∘ σ f g)
--   --   where open Functor ; open Category

--   -- Tms = GrpdFunctor

--   -- _[_] : ∀{Γ Θ} → Ty Θ → Tms Γ Θ → Ty Γ
--   -- A [ σ ] = compFun _ _ _ σ A

open import Function using (flip)

_[_] : ∀{l}{Γ Δ : Groupoid {l}} -> Ty Γ → cat Δ ⟶ cat Γ -> Ty Δ
_[_] = flip compFun

module _ {l} {Γ Δ : Groupoid {l}} {A : Ty Δ} where
  
  open Tm
  open Functor
  open Category

  _[_]' : Tm Δ A -> (σ : cat Γ ⟶ cat Δ) -> Tm Γ (compFun σ A)
  (M [ f ]' ₀') γ = (M ₀') (f ₀ $ γ)
  (M [ f ]' ₁') p = (M ₁') (f ₁ $ p)
  fid' (M [ f ]') γ = {!!} · fid' M (f ₀ $ γ)
    where
      aux1 = fmp0-id Γ (compFun f A) ((M ₀') ((f ₀) γ))
      aux2 = fmp0-id Δ A ((M ₀') ((f ₀) γ))
  f∘'  (M [ f ]') p p' = {!!}

  π₂ : (σ : cat Γ ⟶ cat (Δ ,, A)) → Tm Γ (compFun (π₁ {l} Γ {Δ} {A} σ) A)
  (π₂ σ ₀') γ = snd ((σ ₀) γ)
  (π₂ σ ₁') p = snd ((σ ₁) p)
  fid' (π₂ σ) γ = {!!}
  f∘' (π₂ σ) p q = {!!}
  
  _,s_ : (σ : GrpdFunctor Γ Δ) → Tm Γ (compFun σ A) → GrpdFunctor Γ (Δ ,, A)
  ((σ ,s t) ₀) γ = (σ ₀ $ γ) , (t ₀' $ γ)
  ((σ ,s t) ₁) p = (σ ₁ $ p) , (t ₁' $ p)
  fid (σ ,s t) γ = Σ-≡ (fid σ γ , {!!})
  f∘  (σ ,s t) f g = Σ-≡ (f∘ σ f g , {!!})
