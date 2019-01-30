{-# OPTIONS --cubical #-}
{-# OPTIONS --no-termination-check #-}

module Model where

open import HEq

open import Cubical.Core.Prelude
open import Agda.Primitive
open import Syntax

-- Model of type theory as a CwF
record Model {l} {l'} {l''} {l'''} : Set (lsuc (l ⊔ l' ⊔ l'' ⊔ l''')) where
  field
    Conᴹ : Set l -- (lsuc l)
    Tyᴹ : Conᴹ → Set l' --  (lsuc l)
    Tmsᴹ : Conᴹ → Conᴹ → Set l''
    Tmᴹ : (Γᴹ : Conᴹ) → Tyᴹ Γᴹ → Set l'''

    ◇ᴹ : Conᴹ
    _,ᴹ_ : (Γᴹ : Conᴹ) → Tyᴹ Γᴹ → Conᴹ
    _[_]ᴹ : {Θᴹ Γᴹ : Conᴹ} → Tyᴹ Θᴹ → Tmsᴹ Γᴹ Θᴹ → Tyᴹ Γᴹ
    idᴹ : (Γᴹ : Conᴹ) → Tmsᴹ Γᴹ Γᴹ

    -- the empty context is the terminal object
    εᴹ   : ∀{Γᴹ} → Tmsᴹ Γᴹ ◇ᴹ
    εηᴹ  : ∀{Γᴹ} {σᴹ : Tmsᴹ Γᴹ ◇ᴹ} → σᴹ ≡ εᴹ

    _∘ᴹ_ : ∀{Θᴹ Γᴹ Δᴹ} → Tmsᴹ Θᴹ Δᴹ → Tmsᴹ Γᴹ Θᴹ → Tmsᴹ Γᴹ Δᴹ
    [id]ᴹ : {Γᴹ : Conᴹ} → (Aᴹ : Tyᴹ Γᴹ) → Aᴹ [ idᴹ Γᴹ ]ᴹ ≡ Aᴹ
    [][]ᴹ : ∀{Θᴹ Γᴹ Δᴹ} {σᴹ : Tmsᴹ Θᴹ Δᴹ} {τᴹ : Tmsᴹ Γᴹ Θᴹ} {Aᴹ : Tyᴹ Δᴹ}
          → Aᴹ [ σᴹ ]ᴹ [ τᴹ ]ᴹ ≡ Aᴹ [ σᴹ ∘ᴹ τᴹ ]ᴹ

    -- category laws for substitutions 
    id∘ᴹ : ∀{Γᴹ Δᴹ} → {σᴹ : Tmsᴹ Γᴹ Δᴹ} → idᴹ _ ∘ᴹ σᴹ ≡ σᴹ
    ∘idᴹ : ∀{Γᴹ Δᴹ} → {σᴹ : Tmsᴹ Γᴹ Δᴹ} → σᴹ ∘ᴹ idᴹ _ ≡ σᴹ
    ∘∘ᴹ : ∀{Θᴹ Γᴹ Δᴹ ∇ᴹ} {σᴹ : Tmsᴹ Δᴹ ∇ᴹ} {τᴹ : Tmsᴹ Γᴹ Δᴹ} {δᴹ : Tmsᴹ Θᴹ Γᴹ}
        → (σᴹ ∘ᴹ τᴹ) ∘ᴹ δᴹ ≡ σᴹ ∘ᴹ (τᴹ ∘ᴹ δᴹ)

    -- substitution extension
    _,sᴹ_ : ∀{Γᴹ Δᴹ} {Aᴹ : Tyᴹ Δᴹ} → (σᴹ : Tmsᴹ Γᴹ Δᴹ) → Tmᴹ Γᴹ (Aᴹ [ σᴹ ]ᴹ)
          → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ)
    π₁ᴹ  : ∀{Γᴹ Δᴹ} {Aᴹ : Tyᴹ Δᴹ} → Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ) → Tmsᴹ Γᴹ Δᴹ
    π₂ᴹ : ∀{Γᴹ Δᴹ} {Aᴹ : Tyᴹ Δᴹ} → (σᴹ : Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ)) → Tmᴹ Γᴹ (Aᴹ [ π₁ᴹ σᴹ ]ᴹ)
    π₁βᴹ : ∀{Γᴹ Δᴹ} {σᴹ : Tmsᴹ Γᴹ Δᴹ} {Aᴹ : Tyᴹ Δᴹ} {tᴹ : Tmᴹ Γᴹ (Aᴹ [ σᴹ ]ᴹ)}
         → π₁ᴹ (σᴹ ,sᴹ tᴹ) ≡ σᴹ
    π₂βᴹ : ∀{Γᴹ Δᴹ} {σᴹ : Tmsᴹ Γᴹ Δᴹ} {Aᴹ : Tyᴹ Δᴹ} {tᴹ : Tmᴹ Γᴹ (Aᴹ [ σᴹ ]ᴹ)}
         -- → subst (Tmᴹ Γᴹ) (cong (λ x → Aᴹ [ x ]ᴹ) π₁βᴹ) (π₂ᴹ (σᴹ ,sᴹ tᴹ)) ≡ tᴹ
         → PathP (λ i → Tmᴹ Γᴹ (Aᴹ [ π₁βᴹ {σᴹ = σᴹ} {tᴹ = tᴹ} i ]ᴹ)) (π₂ᴹ (σᴹ ,sᴹ tᴹ)) tᴹ

    πηᴹ : ∀{Γᴹ Δᴹ} {Aᴹ : Tyᴹ Δᴹ} {σᴹ : Tmsᴹ Γᴹ (Δᴹ ,ᴹ Aᴹ)}
        → (π₁ᴹ σᴹ ,sᴹ π₂ᴹ σᴹ) ≡ σᴹ

    _[_]'ᴹ : ∀{Γᴹ Δᴹ} {Aᴹ : Tyᴹ Δᴹ} → Tmᴹ Δᴹ Aᴹ → (σᴹ : Tmsᴹ Γᴹ Δᴹ)
           → Tmᴹ Γᴹ (Aᴹ [ σᴹ ]ᴹ)

    -- ,∘ᴹ : ∀{Γᴹ Δᴹ ∇ᴹ} {τᴹ : Tmsᴹ Γᴹ Δᴹ} {σᴹ : Tmsᴹ ∇ᴹ Γᴹ}
    --     → {Aᴹ : Tyᴹ Δᴹ} {tᴹ : Tmᴹ Γᴹ (Aᴹ [ τᴹ ]ᴹ)}
    --     → _≡_ {A = Tmsᴹ ∇ᴹ (Δᴹ ,ᴹ Aᴹ)}
    --       ((τᴹ ,sᴹ tᴹ) ∘ᴹ σᴹ)
    --       ((τᴹ ∘ᴹ σᴹ) ,sᴹ subst (Tmᴹ ∇ᴹ) [][]ᴹ (tᴹ [ σᴹ ]'ᴹ))

    ,∘₁ᴹ : ∀{Γᴹ Δᴹ ∇ᴹ} {τᴹ : Tmsᴹ Γᴹ Δᴹ} {σᴹ : Tmsᴹ ∇ᴹ Γᴹ} {Aᴹ : Tyᴹ Δᴹ}
         → {tᴹ : Tmᴹ Γᴹ (Aᴹ [ τᴹ ]ᴹ)}
         → π₁ᴹ ((τᴹ ,sᴹ tᴹ) ∘ᴹ σᴹ) ≡ (τᴹ ∘ᴹ σᴹ)

    _[_]'∘ᴹ : ∀{Γᴹ Δᴹ ∇ᴹ} {Aᴹ : Tyᴹ ∇ᴹ} {τᴹ : Tmsᴹ Δᴹ ∇ᴹ}
           → Tmᴹ Δᴹ (Aᴹ [ τᴹ ]ᴹ) → (σᴹ : Tmsᴹ Γᴹ Δᴹ) → Tmᴹ Γᴹ (Aᴹ [ τᴹ ∘ᴹ σᴹ ]ᴹ)
    [][]∘ᴹ : ∀{Γᴹ Δᴹ ∇ᴹ} {Aᴹ : Tyᴹ ∇ᴹ} {τᴹ : Tmsᴹ Δᴹ ∇ᴹ}
           → (tᴹ : Tmᴹ Δᴹ (Aᴹ [ τᴹ ]ᴹ)) → (σᴹ : Tmsᴹ Γᴹ Δᴹ)
           → PathP (λ i → Tmᴹ Γᴹ ([][]ᴹ {σᴹ = τᴹ} {σᴹ} {Aᴹ} i)) (tᴹ [ σᴹ ]'ᴹ) (tᴹ [ σᴹ ]'∘ᴹ)

    ,∘₂ᴹ : ∀{Γᴹ Δᴹ ∇ᴹ} {τᴹ : Tmsᴹ Γᴹ Δᴹ} {σᴹ : Tmsᴹ ∇ᴹ Γᴹ} {Aᴹ : Tyᴹ Δᴹ}
         → {tᴹ : Tmᴹ Γᴹ (Aᴹ [ τᴹ ]ᴹ)}
         → PathP (λ i → Tmᴹ ∇ᴹ (Aᴹ [ ,∘₁ᴹ {τᴹ = τᴹ} {σᴹ} {Aᴹ} {tᴹ} i ]ᴹ))
                 (π₂ᴹ ((τᴹ ,sᴹ tᴹ) ∘ᴹ σᴹ))
                 (tᴹ [ σᴹ ]'∘ᴹ)

    π₂∘ᴹ : ∀{Γ Δ ∇} {A : Tyᴹ ∇} → {τ : Tmsᴹ Δ ∇}
         → (σ : Tmsᴹ Γ (Δ ,ᴹ (A [ τ ]ᴹ)))
        → Tmᴹ Γ (A [ τ ∘ᴹ π₁ᴹ σ ]ᴹ)
    π₂≡ᴹ : ∀{Γ Δ ∇} {A : Tyᴹ ∇} → {τ : Tmsᴹ Δ ∇}
         → (σ : Tmsᴹ Γ (Δ ,ᴹ (A [ τ ]ᴹ)))
        → PathP (λ i → Tmᴹ Γ ([][]ᴹ {σᴹ = τ} {π₁ᴹ σ} {A} i)) (π₂ᴹ σ) (π₂∘ᴹ σ)

    Uᴹ : ∀{Γ} → Tyᴹ Γ
    U[]ᴹ : ∀{Δᴹ Γᴹ} (σᴹ : Tmsᴹ Γᴹ Δᴹ) → Uᴹ [ σᴹ ]ᴹ ≡ Uᴹ

    _[_]'Uᴹ : ∀{Γ Δ} → Tmᴹ Δ Uᴹ → (σ : Tmsᴹ Γ Δ) → Tmᴹ Γ Uᴹ
    []U≡ᴹ : ∀{Γ Δ} → (t : Tmᴹ Δ Uᴹ) → (σ : Tmsᴹ Γ Δ)
          → PathP (λ i → Tmᴹ Γ (U[]ᴹ σ i)) (t [ σ ]'ᴹ) (t [ σ ]'Uᴹ)

    Πᴹ : ∀{Γ} (A : Tyᴹ Γ) (B : Tyᴹ (Γ ,ᴹ A)) → Tyᴹ Γ
    Π[]ᴹ : ∀{Γ Δ} (A : Tyᴹ Γ) (B : Tyᴹ (Γ ,ᴹ A)) → (σ : Tmsᴹ Δ Γ)
        → let _↑ᴹ_ : ∀{Γ Δ} → (σ : Tmsᴹ Γ Δ) → (A : Tyᴹ Δ) → Tmsᴹ (Γ ,ᴹ (A [ σ ]ᴹ)) (Δ ,ᴹ A)
              σ ↑ᴹ A = (σ ∘ᴹ π₁ᴹ (idᴹ _)) ,sᴹ (π₂∘ᴹ (idᴹ _))
          in (Πᴹ A B) [ σ ]ᴹ ≡ Πᴹ (A [ σ ]ᴹ) (B [ σ ↑ᴹ A ]ᴹ)

    Elᴹ : ∀{Γ} → (A : Tmᴹ Γ Uᴹ) → Tyᴹ Γ
    El[]ᴹ : ∀{Γ Δ} → (A : Tmᴹ Γ Uᴹ) → (σ : Tmsᴹ Δ Γ)
         → ((Elᴹ A) [ σ ]ᴹ) ≡ Elᴹ (A [ σ ]'Uᴹ)

    lamᴹ : ∀{Γ} {A : Tyᴹ Γ} {B : Tyᴹ (Γ ,ᴹ A)} → Tmᴹ (Γ ,ᴹ A) B → Tmᴹ Γ (Πᴹ A B)
    appᴹ : ∀{Γ} {A : Tyᴹ Γ} {B : Tyᴹ (Γ ,ᴹ A)} → Tmᴹ Γ (Πᴹ A B) → Tmᴹ (Γ ,ᴹ A) B
    βᴹ   : ∀{Γ} {A : Tyᴹ Γ} {B : Tyᴹ (Γ ,ᴹ A)} (t : Tmᴹ (Γ ,ᴹ A) B) → appᴹ (lamᴹ t) ≡ t
    ηᴹ   : ∀{Γ} {A : Tyᴹ Γ} {B : Tyᴹ (Γ ,ᴹ A)} (f : Tmᴹ Γ (Πᴹ A B)) → lamᴹ (appᴹ f) ≡ f

variable
  Θ Γ Δ : Con

module _ {l} {l'} {l''} {l'''} (M : Model {l} {l'} {l''} {l'''}) where
  open Model M

  mutual
    con : Con → Conᴹ
    con ◇ = ◇ᴹ
    con (Γ , A) = (con Γ) ,ᴹ (ty A)

    ty : Ty Γ → Tyᴹ (con Γ)
    ty (A [ x ]) = (ty A) [ tms x ]ᴹ
    ty ([id] Γ A i) = [id]-proof (ty A) i
    ty ([][] {σ = σ} {τ = τ} {A = A} i) = [][]-proof {σᴹ = tms σ} {tms τ} {ty A} i
    ty U = Uᴹ
    ty (U[] σ i) = U[]ᴹ (tms σ) i
    ty (Π A B) = Πᴹ (ty A) (ty B)
    ty (Π[] A B σ i) = Π[]-proof (ty A) (ty B) (tms σ) i
    ty (El A) = Elᴹ (tm A)
    ty (El[] A σ i) = El[]-proof (tm A) (tms σ) i

    tms : Tms Γ Δ → Tmsᴹ (con Γ) (con Δ)
    tms (id Γ) = idᴹ (con Γ)
    tms ε = εᴹ
    tms (x ∘ y) = tms x ∘ᴹ tms y
    tms (∘∘ {σ = σ} {τ} {δ} i) = ∘∘ᴹ {σᴹ = tms σ} {tms τ} {tms δ} i
    tms (id∘ {σ = σ} i) = id∘ᴹ {σᴹ = tms σ} i
    tms (∘id {σ = σ} i) = ∘idᴹ {σᴹ = tms σ} i
    tms (π₁ σ) = π₁ᴹ (tms σ)
    tms (εη {σ = σ} i) = εηᴹ {σᴹ = tms σ} i
    tms (_,_ σ t) = tms σ ,sᴹ tm t
    tms (π₁β {Γ = Γ} {σ = σ} {A} {t} i) = π₁βᴹ {σᴹ = tms σ} {ty A} {tm t} i
    tms (πη {Γ = Γ} {Δ = Δ} {A = A} {σ} i) = πη-proof {Aᴹ = ty A} {tms σ} i
    tms (,∘₁ {Γ = Γ} {Δ} {∇} {τ = τ} {σ} {A} {t} i) =
      ,∘₁-proof {τᴹ = tms τ} {tms σ} {ty A} {tm t} i

    tm : {A : Ty Γ} → Tm Γ A → Tmᴹ (con Γ) (ty A)
    tm (t [ σ ]') = tm t [ tms σ ]'ᴹ
    tm (t [ σ ]'∘) = tm t [ tms σ ]'∘ᴹ
    tm (π₂ σ) = π₂ᴹ (tms σ)
    tm (π₂β {σ = σ} {A} {t} i) = π₂β-proof {σᴹ = tms σ} {ty A} {tm t} i
    tm (,∘₂ {τ = τ} {σ} {A} {t} i) =
      ,∘₂-proof {τᴹ = tms τ} {tms σ} {ty A} {tm t} i
    tm ([][]∘ x σ i) = [][]∘-proof (tm x) (tms σ) i
    tm (x [ σ ]'U) = tm x [ tms σ ]'Uᴹ
    tm ([]U≡ x σ i) = []U≡ᴹ (tm x) (tms σ) i
    tm (π₂∘ σ) = π₂∘ᴹ (tms σ)
    tm (π₂≡ {τ = τ} σ i) = π₂≡-proof {τ = tms τ} (tms σ) i
    tm (lam t) = lamᴹ (tm t)
    tm (app f) = appᴹ (tm f)
    tm (β t i) = βᴹ (tm t) i
    tm (η f i) = ηᴹ (tm f) i

    [id]-proof = [id]ᴹ
    [][]-proof = [][]ᴹ
    ,∘₁-proof = ,∘₁ᴹ
    ,∘₂-proof = ,∘₂ᴹ
    [][]∘-proof = [][]∘ᴹ
    π₂β-proof = π₂βᴹ
    πη-proof = πηᴹ
    π₂≡-proof = π₂≡ᴹ
    Π[]-proof = Π[]ᴹ
    El[]-proof = El[]ᴹ
