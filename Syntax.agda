{-# OPTIONS --cubical #-}

module Syntax where

open import Cubical.Core.Prelude

data Con : Set
data Tms : Con → Con → Set
data Ty  : Con -> Set
data Tm : (Γ : Con) → Ty Γ → Set

_,con_ : (Γ : Con) → Ty Γ → Con
_[_]aux : ∀{Θ Γ} → Ty Θ → Tms Γ Θ → Ty Γ
_[_]'aux : ∀{Γ Δ} {A : Ty Δ} → Tm Δ A → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]aux)
_,sub_ : ∀{Γ Δ} {A : Ty Δ} → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]aux) → Tms Γ (Δ ,con A)
π₁aux  : ∀{Γ Δ} {A : Ty Δ} → Tms Γ (Δ ,con A) → Tms Γ Δ
π₂aux : ∀{Γ Δ} {A : Ty Δ} → (σ : Tms Γ (Δ ,con A)) → Tm Γ (A [ π₁aux σ ]aux)
idaux : ∀{Γ} → Tms Γ Γ
_∘aux_ : ∀{Θ Γ Δ} → Tms Θ Δ → Tms Γ Θ → Tms Γ Δ
[][]aux : ∀{Θ Γ Δ} {σ : Tms Θ Δ} {τ : Tms Γ Θ} {A : Ty Δ}
        → A [ σ ]aux [ τ ]aux ≡ A [ σ ∘aux τ ]aux

,∘₁aux : ∀{Γ Δ ∇} {τ : Tms Γ Δ} {σ : Tms ∇ Γ} {A : Ty Δ} {t : Tm Γ (A [ τ ]aux)}
       → π₁aux ((τ ,sub t) ∘aux σ) ≡ (τ ∘aux σ)

_[_]'∘aux : ∀{Γ Δ ∇} {A : Ty ∇} {τ : Tms Δ ∇}
       → Tm Δ (A [ τ ]aux) → (σ : Tms Γ Δ) → Tm Γ (A [ τ ∘aux σ ]aux)

Uaux : ∀{Γ} → Ty Γ
Elaux : ∀{Γ} → (A : Tm Γ Uaux) → Ty Γ
_[_]'Uaux : ∀{Γ Δ} → Tm Δ Uaux → Tms Γ Δ → Tm Γ Uaux

-- π₁βaux : ∀{Γ Δ} {σ : Tms Γ Δ} {A : Ty Δ} {t : Tm Γ (A [ σ ]aux)}
--        → π₁aux (σ ,sub t) ≡ σ

data Con where
  ◇   : Con
  _,_ : (Γ : Con) → Ty Γ → Con

data Tms where
  _∘_ : ∀{Θ Γ Δ} → Tms Θ Δ → Tms Γ Θ → Tms Γ Δ
  id  : ∀ Γ → Tms Γ Γ
  ε   : ∀{Γ} → Tms Γ ◇
  _,_ : ∀{Γ Δ} {A : Ty Δ} → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]aux) → Tms Γ (Δ , A)
  π₁  : ∀{Γ Δ} {A : Ty Δ} → Tms Γ (Δ , A) → Tms Γ Δ

  ∘∘ : ∀{Θ Γ Δ ∇} {σ : Tms Δ ∇} {τ : Tms Γ Δ} {δ : Tms Θ Γ}
     → (σ ∘ τ) ∘ δ ≡ σ ∘ (τ ∘ δ)
  id∘ : ∀{Γ Δ} → {σ : Tms Γ Δ} → id _ ∘ σ ≡ σ
  ∘id : ∀{Γ Δ} → {σ : Tms Γ Δ} → σ ∘ id _ ≡ σ
  εη  : ∀{Γ} {σ : Tms Γ ◇} → σ ≡ ε
  π₁β : ∀{Γ Δ} {σ : Tms Γ Δ} {A : Ty Δ} {t : Tm Γ (A [ σ ]aux)}
      → π₁ (σ , t) ≡ σ
  πη  : ∀{Γ Δ} {A : Ty Δ} {σ : Tms Γ (Δ ,con A)} → (π₁aux σ ,sub π₂aux σ) ≡ σ
  -- ,∘  : ∀{Γ Δ ∇} {τ : Tms Γ Δ} {σ : Tms ∇ Γ} {A : Ty Δ} {t : Tm Γ (A [ τ ]aux)}
  --     → (τ , t) ∘ σ ≡ ((τ ∘aux σ) , subst (Tm ∇) [][]aux (t [ σ ]'aux))
  ,∘₁  : ∀{Γ Δ ∇} {τ : Tms Γ Δ} {σ : Tms ∇ Γ} {A : Ty Δ} {t : Tm Γ (A [ τ ]aux)}
       → π₁ ((τ , t) ∘ σ) ≡ (τ ∘aux σ)

wk : ∀{Γ} {A : Ty Γ} → Tms (Γ , A) Γ
wk = π₁ (id _)

vz : ∀{Γ} {A : Ty Γ} → Tm (Γ , A) (A [ wk ]aux)
vs : ∀{Γ} {A B : Ty Γ} → Tm Γ A → Tm (Γ , B) (A [ wk ]aux)

_↑_ : ∀{Γ Δ} → (σ : Tms Γ Δ) → (A : Ty Δ) → Tms (Γ , (A [ σ ]aux)) (Δ , A)

data Ty where
  -- terms of the substitution calculus
  _[_] : ∀{Θ Γ} → Ty Θ → Tms Γ Θ → Ty Γ

  [][] : ∀{Θ Γ Δ} {σ : Tms Θ Δ} {τ : Tms Γ Θ} {A : Ty Δ}
       → (A [ σ ]) [ τ ] ≡ A [ σ ∘ τ ]
  [id] : ∀ Γ → (A : Ty Γ) → A [ id _ ] ≡ A

  -- type formers
  U : ∀{Γ} → Ty Γ
  U[] : ∀{Δ Γ} (σ : Tms Γ Δ) → U [ σ ] ≡ U

  Π : ∀{Γ} (A : Ty Γ) (B : Ty (Γ , A)) → Ty Γ
  Π[] : ∀{Γ Δ} (A : Ty Γ) (B : Ty (Γ , A)) → (σ : Tms Δ Γ)
      → (Π A B) [ σ ]aux ≡ Π (A [ σ ]aux) (B [ σ ↑ A ]aux)

  El : ∀{Γ} → (A : Tm Γ U) → Ty Γ
  El[] : ∀{Γ Δ} → (A : Tm Γ Uaux) → (σ : Tms Δ Γ)
       → ((Elaux A) [ σ ]) ≡ Elaux (A [ σ ]'Uaux)

data Tm where
  _[_]'  : ∀{Γ Δ} {A : Ty Δ} → Tm Δ A → (σ : Tms Γ Δ) → Tm Γ (A [ σ ])
  _[_]'∘ : ∀{Γ Δ ∇} {A : Ty ∇} {τ : Tms Δ ∇}
         → Tm Δ (A [ τ ]) → (σ : Tms Γ Δ) → Tm Γ (A [ τ ∘ σ ])
  _[_]'U : ∀{Γ Δ} → Tm Δ U → (σ : Tms Γ Δ) → Tm Γ U
  [][]∘ : ∀{Γ Δ ∇} {A : Ty ∇} {τ : Tms Δ ∇}
         → (t : Tm Δ (A [ τ ])) → (σ : Tms Γ Δ)
         → PathP (λ i → Tm Γ ([][] {σ = τ} {σ} {A} i)) (t [ σ ]') (t [ σ ]'∘)
  []U≡  : ∀{Γ Δ} → (t : Tm Δ U) → (σ : Tms Γ Δ)
        → PathP (λ i → Tm Γ (U[] σ i)) (t [ σ ]') (t [ σ ]'U)

  π₂  : ∀{Γ Δ} {A : Ty Δ} → (σ : Tms Γ (Δ , A)) → Tm Γ (A [ π₁ σ ]aux)
  π₂∘ : ∀{Γ Δ ∇} {A : Ty ∇} → {τ : Tms Δ ∇} → (σ : Tms Γ (Δ ,con (A [ τ ]aux)))
      → Tm Γ (A [ τ ∘aux π₁aux σ ]aux)
  π₂≡ : ∀{Γ Δ ∇} {A : Ty ∇} → {τ : Tms Δ ∇} → (σ : Tms Γ (Δ ,con (A [ τ ]aux)))
      → PathP (λ i → Tm Γ ([][]aux {σ = τ} {π₁aux σ} {A} i)) (π₂aux σ) (π₂∘ σ)

  π₂β : ∀{Γ Δ} {σ : Tms Γ Δ} {A : Ty Δ} {t : Tm Γ (A [ σ ]aux)}
      → PathP (λ i → Tm Γ (A [ π₁β {σ = σ} {t = t} i ]aux)) (π₂ (σ , t)) t

  ,∘₂  : ∀{Γ Δ ∇} {τ : Tms Γ Δ} {σ : Tms ∇ Γ} {A : Ty Δ} {t : Tm Γ (A [ τ ]aux)}
       → PathP (λ i → Tm ∇ (A [ ,∘₁aux {τ = τ} {σ} {A} {t} i ]aux))
           (π₂aux ((τ ,sub t) ∘aux σ))
           (t [ σ ]'∘aux)

  -- term constructors
  lam : ∀{Γ} {A : Ty Γ} {B : Ty (Γ , A)} → Tm (Γ , A) B → Tm Γ (Π A B)
  app : ∀{Γ} {A : Ty Γ} {B : Ty (Γ , A)} → Tm Γ (Π A B) → Tm (Γ , A) B
  β   : ∀{Γ} {A : Ty Γ} {B : Ty (Γ , A)} (t : Tm (Γ , A) B) → app (lam t) ≡ t
  η   : ∀{Γ} {A : Ty Γ} {B : Ty (Γ , A)} (f : Tm Γ (Π A B)) → lam (app f) ≡ f

_[_]aux = _[_]
_[_]'aux = _[_]'
_,con_ = _,_
_,sub_ = _,_
π₁aux = π₁
π₂aux = π₂
idaux = id _
_∘aux_ = _∘_
[][]aux = [][]
,∘₁aux = ,∘₁
_[_]'∘aux = _[_]'∘
Uaux = U
Elaux = El
_[_]'Uaux = _[_]'U

vz = π₂ (id _)
vs = λ x → x [ wk ]'
_↑_ {Γ} {Δ} σ A = (σ ∘ wk) , π₂∘ (id (Γ , A [ σ ]aux))
