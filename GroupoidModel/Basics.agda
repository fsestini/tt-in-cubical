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
      fid' : ∀ γ → PathOver {C = cat (A ₀ $ γ)}
                     (_₁' (gid Γ γ)) (fmp0-id Γ A (γ ₀')) (gid ((A ₀) γ) (_₀' γ))
      f∘'  : ∀{γ γ' γ''} → (p : GMorph Γ γ γ') (p' : GMorph Γ γ' γ'')
           → PathOver {C = cat ((A ₀) γ'')}
                      (_₁' (_∘_ (cat Γ) p' p))
                      (cong (_$ γ ₀') (cong _₀ (f∘ A p' p)))
                      (_∘_ (cat ((A ₀) γ'')) (_₁' p') (((fmp Γ A p') ₁) (_₁' p)))

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

module _ {l} (Γ : Groupoid {l}) (A : Ty {l} Γ) (a : Tm Γ A) where

  open Functor
  open Tm

  ,,fun : GrpdFunctor Γ (Γ ,, A)
  (,,fun ₀) γ = γ , (a ₀' $ γ)
  (,,fun ₁) p = p , (a ₁' $ p)
  fid ,,fun γ = {!!}
  f∘ ,,fun p q = {!!}

module _ {l} -- (H : (A : Groupoid {l}) -> Functor (cat (gcross A A)) (Grpd {l}))
             (Γ : Groupoid {l}) (A : Ty {l} Γ) where

  open Functor
  open Category

  tms-fst : GrpdFunctor (Γ ,, A) Γ
  tms-fst = π₁ {l} (Γ ,, A) {Γ} {A} (IdFunctor (cat (Γ ,, A)))

  rearrange : GrpdFunctor ((Γ ,, A) ,, compFun tms-fst A)
                          (gcross (Γ ,, A) (Γ ,, A))
  (rearrange ₀) ((γ , x) , y) = (γ , x) , (γ , y)
  (rearrange ₁) ((p , q1) , q2) = (p , q1) , (p , q2)
  fid rearrange ((γ , x) , y) = Σ-≡ ((Σ-≡ (refl , transpRefl _ _)) ,
                                      Σ-≡ (transpRefl _ _ , {!!}))
  f∘ rearrange ((p , q1) , q2) ((p' , q1') , q2') = {!!}
  

  -- uncurry,, : Ty {l} ((Γ ,, A) ,, compFun tms-fst A)
  -- (uncurry,, ₀) ((γ , x) , y) = (H ((A ₀) γ)) ₀ $ x , y
  -- (uncurry,, ₁) {(γ , x) , y} {(γ' , x') , y'} ((p , q1) , q2) =
  --   let aux = (H ((A ₀) γ') ₁) (q1 , q2) in compFun {!!} aux
  -- fid uncurry,, = {!!}
  -- f∘ uncurry,, = {!!}

open import Function using (flip)

_[_] : ∀{l}{Γ Δ : Groupoid {l}} -> Ty Γ → cat Δ ⟶ cat Γ -> Ty Δ
_[_] = flip compFun

module _ {l} {Γ Δ : Groupoid {l}} {A : Ty Δ} where
  
  open Tm
  open Functor
  -- open Category

  _[_]' : Tm Δ A -> (σ : cat Γ ⟶ cat Δ) -> Tm Γ (compFun σ A)
  (M [ f ]' ₀') γ = (M ₀') (f ₀ $ γ)
  (M [ f ]' ₁') p = (M ₁') (f ₁ $ p)
  fid' (M [ f ]') γ = substPathOver (strct ((A ₀) ((f ₀) γ))) _ goal'
    where
      aux = compPathOver (symPathOver (fid' M ((f ₀) γ))) (fid' M (f ₀ $ γ))
      aux' = MkPathOver (let xxx = ap (M ₁') (fid f γ) in fromPathP xxx)
      goal' = compPathOver aux' (compPathOver (fid' M ((f ₀) γ)) aux)
  f∘'  (M [ f ]') {γ'' = γ''} p p' =
    substPathOver (strct ((A ₀) ((f ₀) γ''))) _
     (compPathOver (MkPathOver (fromPathP (ap (M ₁') (f∘ f p' p))))
                   (f∘' M ((f ₁) p) ((f ₁) p')))

  π₂ : (σ : cat Γ ⟶ cat (Δ ,, A)) → Tm Γ (compFun (π₁ {l} Γ {Δ} {A} σ) A)
  (π₂ σ ₀') γ = snd ((σ ₀) γ)
  (π₂ σ ₁') p = snd ((σ ₁) p)
  fid' (π₂ σ) γ = substPathOver (strct ((A ₀) (proj₁ ((σ ₀) γ)))) _
    (compPathOver (MkPathOver (fromPathP (ap snd (fid σ γ)))) collapsePathOver)
  f∘' (π₂ σ) {γ'' = γ''} p q = {!!} -- substPathOver {!!} _ {!!}
      -- (compPathOver (MkPathOver (fromPathP (ap snd (f∘ σ q p)))) {!!})
    where open Category (cat ((A ₀) (proj₁ ((σ ₀) γ''))))
    
  _,s_ : (σ : GrpdFunctor Γ Δ) → Tm Γ (compFun σ A) → GrpdFunctor Γ (Δ ,, A)
  ((σ ,s t) ₀) γ = (σ ₀ $ γ) , (t ₀' $ γ)
  ((σ ,s t) ₁) p = (σ ₁ $ p) , (t ₁' $ p)
  fid (σ ,s t) γ = Σ-≡ (fid σ γ , {!!})
  f∘  (σ ,s t) f g = Σ-≡ (f∘ σ f g , {!!})
