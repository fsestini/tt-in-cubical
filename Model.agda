{-# OPTIONS --cubical #-}
{-# OPTIONS --no-termination-check #-}

module Model where

open import Utils

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

    -- ,∘₂ᴹ : ∀{Γᴹ Δᴹ ∇ᴹ} {τᴹ : Tmsᴹ Γᴹ Δᴹ} {σᴹ : Tmsᴹ ∇ᴹ Γᴹ} {Aᴹ : Tyᴹ Δᴹ}
    --      → {tᴹ : Tmᴹ Γᴹ (Aᴹ [ τᴹ ]ᴹ)}
    --      → PathP (λ i → Tmᴹ ∇ᴹ (Aᴹ [ ,∘₁ᴹ {τᴹ = τᴹ} {σᴹ} {Aᴹ} {tᴹ} i ]ᴹ))
    --              (π₂ᴹ ((τᴹ ,sᴹ tᴹ) ∘ᴹ σᴹ))
    --              (tᴹ [ σᴹ ]'∘ᴹ)

    ,∘₂ᴹ  : ∀{Γ Δ ∇} {τ : Tmsᴹ Γ Δ} {σ : Tmsᴹ ∇ Γ} {A : Tyᴹ Δ} {t : Tmᴹ Γ (A [ τ ]ᴹ)}
         → subst (Tmᴹ ∇)
                 (cong (λ x → A [ x ]ᴹ) ,∘₁ᴹ · sym [][]ᴹ)
                 (π₂ᴹ ((τ ,sᴹ t) ∘ᴹ σ))
         ≡ (t [ σ ]'ᴹ)

    π₂∘ᴹ : ∀{Γ Δ ∇} {A : Tyᴹ ∇} → {τ : Tmsᴹ Δ ∇}
         → (σ : Tmsᴹ Γ (Δ ,ᴹ (A [ τ ]ᴹ)))
        → Tmᴹ Γ (A [ τ ∘ᴹ π₁ᴹ σ ]ᴹ)
    π₂≡ᴹ : ∀{Γ Δ ∇} {A : Tyᴹ ∇} → {τ : Tmsᴹ Δ ∇}
         → (σ : Tmsᴹ Γ (Δ ,ᴹ (A [ τ ]ᴹ)))
        → PathP (λ i → Tmᴹ Γ ([][]ᴹ {σᴹ = τ} {π₁ᴹ σ} {A} i)) (π₂ᴹ σ) (π₂∘ᴹ σ)

    Uᴹ : ∀{Γ} → Tyᴹ Γ
    U[]ᴹ : ∀{Δᴹ Γᴹ} (σᴹ : Tmsᴹ Γᴹ Δᴹ) → Uᴹ [ σᴹ ]ᴹ ≡ Uᴹ

    Πᴹ : ∀{Γ} (A : Tyᴹ Γ) (B : Tyᴹ (Γ ,ᴹ A)) → Tyᴹ Γ
    Π[]ᴹ : ∀{Γ Δ} (A : Tyᴹ Γ) (B : Tyᴹ (Γ ,ᴹ A)) → (σ : Tmsᴹ Δ Γ)
         -> let _↑ᴹ_ : ∀{Γ Δ} → (σ : Tmsᴹ Γ Δ) → (A : Tyᴹ Δ) → Tmsᴹ (Γ ,ᴹ (A [ σ ]ᴹ)) (Δ ,ᴹ A)
                σ ↑ᴹ A = (σ ∘ᴹ π₁ᴹ (idᴹ _)) ,sᴹ subst (Tmᴹ _) [][]ᴹ (π₂ᴹ (idᴹ (_ ,ᴹ (A [ σ ]ᴹ))))
            in (Πᴹ A B) [ σ ]ᴹ ≡ Πᴹ (A [ σ ]ᴹ) (B [ σ ↑ᴹ A ]ᴹ)

    Elᴹ : ∀{Γ} → (A : Tmᴹ Γ Uᴹ) → Tyᴹ Γ

    El[]ᴹ : ∀{Γ Δ} → (A : Tmᴹ Γ Uᴹ) → (σ : Tmsᴹ Δ Γ)
          → ((Elᴹ A) [ σ ]ᴹ) ≡ Elᴹ (subst (Tmᴹ Δ) (U[]ᴹ σ) (A [ σ ]'ᴹ))

    lamᴹ : ∀{Γ} {A : Tyᴹ Γ} {B : Tyᴹ (Γ ,ᴹ A)} → Tmᴹ (Γ ,ᴹ A) B → Tmᴹ Γ (Πᴹ A B)
    appᴹ : ∀{Γ} {A : Tyᴹ Γ} {B : Tyᴹ (Γ ,ᴹ A)} → Tmᴹ Γ (Πᴹ A B) → Tmᴹ (Γ ,ᴹ A) B
    βᴹ   : ∀{Γ} {A : Tyᴹ Γ} {B : Tyᴹ (Γ ,ᴹ A)} (t : Tmᴹ (Γ ,ᴹ A) B) → appᴹ (lamᴹ t) ≡ t
    ηᴹ   : ∀{Γ} {A : Tyᴹ Γ} {B : Tyᴹ (Γ ,ᴹ A)} (f : Tmᴹ Γ (Πᴹ A B)) → lamᴹ (appᴹ f) ≡ f

    lam[]ᴹ : ∀{Δ Γ} {A : Tyᴹ Γ} {B : Tyᴹ (Γ ,ᴹ A)} (t : Tmᴹ (Γ ,ᴹ A) B) (σ : Tmsᴹ Δ Γ)
          -> let _↑ᴹ_ : ∀{Γ Δ} → (σ : Tmsᴹ Γ Δ) → (A : Tyᴹ Δ) → Tmsᴹ (Γ ,ᴹ (A [ σ ]ᴹ)) (Δ ,ᴹ A)
                 σ ↑ᴹ A = (σ ∘ᴹ π₁ᴹ (idᴹ _)) ,sᴹ subst (Tmᴹ _) [][]ᴹ (π₂ᴹ (idᴹ (_ ,ᴹ (A [ σ ]ᴹ))))
             in ((lamᴹ t) [ σ ]'ᴹ) ≡ subst (Tmᴹ Δ) (sym (Π[]ᴹ A B σ)) (lamᴹ (t [ σ ↑ᴹ A ]'ᴹ))

    ty-trunc : ∀{Γ} -> isSet (Tyᴹ Γ)

variable
  Θ Γ Δ : Con

module _ {l l'} (A : Set l) (aset : isSet A) where

  K : (M : A) (C : M ≡ M -> Set l') -> C refl -> (loop : M ≡ M) -> C loop
  K M C h p = subst C (aset _ _ _ _) h

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
    ty (Π[] A B σ i) = Π[]-proof A B σ i
    ty (El A) = Elᴹ (tm A)
    ty (El[] A σ i) = El-proof σ A i

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
    tm (π₂ σ) = π₂ᴹ (tms σ)
    tm (π₂β {σ = σ} {A} {t} i) = π₂β-proof {σᴹ = tms σ} {ty A} {tm t} i
    tm (,∘₂ {∇ = ∇} {τ = τ} {σ} {A} {t} i) = ,∘₂ᴹ-proof {∇ = ∇} {τ = τ} {σ} {A} {t} i
    tm (lam t) = lamᴹ (tm t)
    tm (app f) = appᴹ (tm f)
    tm (β t i) = βᴹ (tm t) i
    tm (η f i) = ηᴹ (tm f) i
    tm (lam[] {A = A} {B} t σ i) = lam[]-proof A B σ t i

    [id]-proof = [id]ᴹ
    [][]-proof = [][]ᴹ
    ,∘₁-proof = ,∘₁ᴹ
    ,∘₂-proof = ,∘₂ᴹ
    [][]∘-proof = [][]∘ᴹ
    π₂β-proof = π₂βᴹ
    πη-proof = πηᴹ
    π₂≡-proof = π₂≡ᴹ

    lamᴹsub : ∀{Γ Δ} (A : Tyᴹ _) (B : Tyᴹ _) (t : Tmᴹ (Γ ,ᴹ A) B) (σ : Tmsᴹ _ _)
              {γ τ : Tmsᴹ (Δ ,ᴹ (A [ σ ]ᴹ)) (Γ ,ᴹ A)} (p : γ ≡ τ)
            -> lamᴹ (t [ γ ]'ᴹ) ≡ subst (Tmᴹ _) (ap (λ z → Πᴹ _ (B [ z ]ᴹ)) (sym p)) (lamᴹ (t [ τ ]'ᴹ))
    lamᴹsub {Γ} {Δ} A B t σ {γ} =
      J (λ τ' p' → lamᴹ (t [ γ ]'ᴹ) ≡ subst (Tmᴹ _) (ap (λ z → Πᴹ _ (B [ z ]ᴹ)) (sym p')) (lamᴹ (t [ τ' ]'ᴹ)))
        (sym (transpRefl (Tmᴹ _ (Πᴹ _ _)) (lamᴹ (t [ γ ]'ᴹ))))
      
    swap-subst : ∀{Γ Ty1 Ty2} {t : Tm Γ Ty1}
      -> (p : Ty1 ≡ Ty2) (q : ty Ty1 ≡ ty Ty2)
      -> tm (subst (Tm Γ) p t) ≡ subst (Tmᴹ (con Γ)) q (tm t)
    swap-subst {Γ} {Ty1} {_} {t} = J (λ Ty2' p' → (q : ty Ty1 ≡ ty Ty2')
      -> tm (subst (Tm Γ) p' t) ≡ subst (Tmᴹ (con Γ)) q (tm t))
        λ q -> K (Tyᴹ (con Γ)) (ty-trunc {con Γ}) (ty Ty1)
            (λ q -> tm (subst (Tm Γ) refl t) ≡ subst (Tmᴹ (con Γ)) q (tm t))
              (ap tm (transpRefl _ t) · sym (transpRefl _ (tm t))) q

    Π[]-proof : ∀{Γ Δ} (A : Ty Γ) (B : Ty (Γ , A)) (σ : Tms Δ Γ)
              → ty ((Π A B) [ σ ]) ≡ ty (Π (A [ σ ]) (B [ σ ↑ A ]))
    Π[]-proof {Γ} {Δ} A B σ =
      Π[]ᴹ (ty A) (ty B) (tms σ) · ap (λ x → Πᴹ _ (ty B [ _ ,sᴹ x ]ᴹ))
        (sym (swap-subst {t = π₂ (id (Δ , (A [ σ ]aux)))} [][] [][]ᴹ))
       
    El-proof : ∀{Γ Δ} (σ : Tms Γ Δ) (A : Tm Δ Uaux)
             -> ty (Elaux A [ σ ]) ≡ ty (Elaux (subst (Tm Γ) ([]Uaux σ) (A [ σ ]'aux)))
    El-proof σ A = El[]ᴹ (tm A) (tms σ) · ap Elᴹ (sym (swap-subst {t = A [ σ ]'} (U[] σ) (U[]ᴹ (tms σ))))

    ,∘₂ᴹ-proof : ∀{Γ Δ ∇} {τ : Tms Γ Δ} {σ : Tms ∇ Γ} {A : Ty Δ} {t : Tm Γ (A [ τ ]aux)}
         -> tm (subst (Tm ∇) (cong (_[_] A) ,∘₁ · sym [][]) (π₂ ((τ , t) ∘ σ))) ≡ tm (t [ σ ]')
    ,∘₂ᴹ-proof {Γ} {Δ} {∇} {τ} {σ} {A} {t} =
      swap-subst {t = π₂ ((τ , t) ∘ σ)} (cong (_[_] A) ,∘₁ · sym [][])
        (cong (_[_]ᴹ (ty A)) ,∘₁ᴹ · sym [][]ᴹ) · ,∘₂ᴹ {τ = tms τ} {tms σ} {ty A} {tm t}

    open import Function using (_$_)
    
    lam[]-proof : ∀{Γ Δ} (A : Ty Δ) (B : Ty (Δ , A)) (σ : Tms Γ Δ) (t : Tm (Δ , A) B)
                -> tm ((lam t) [ σ ]') ≡ tm (subst (Tm _) (sym (Π[] A B σ)) (lam (t [ σ ↑ A ]'aux)))
    lam[]-proof {Γ} {Δ} A B σ t = begin
      (lamᴹ (tm t) [ tms σ ]'ᴹ)
        ≡⟨ lam[]ᴹ {A = ty A} {B = ty B} (tm t) (tms σ) ⟩
      (subst (Tmᴹ _) (sym (Π[]ᴹ (ty A) (ty B) (tms σ))) (lamᴹ ((tm t) [ tms σ ↑ᴹ ty A ]'ᴹ)))
        ≡⟨ ap (subst (Tmᴹ _) (sym (Π[]ᴹ (ty A) (ty B) (tms σ)))) (lamᴹsub (ty A) (ty B) (tm t) (tms σ) aux) ⟩
      (subst (Tmᴹ _) (sym (Π[]ᴹ (ty A) (ty B) (tms σ))) (subst (Tmᴹ _) (ap (λ z → Πᴹ (ty (A [ σ ])) (ty B [ z ]ᴹ)) (sym aux)) (tm (lam (t [ σ ↑ A ]')))))
        ≡⟨ {!!} ⟩
      (subst (Tmᴹ _) (ap (λ z → Πᴹ (ty (A [ σ ])) (ty B [ z ]ᴹ)) (sym aux) · sym (Π[]ᴹ (ty A) (ty B) (tms σ))) (tm (lam (t [ σ ↑ A ]'))))
        ≡⟨ sym (swap-subst {t = lam (t [ σ ↑ A ]')} (sym (Π[] A B σ)) (ap (λ z → Πᴹ (ty (A [ σ ])) (ty B [ z ]ᴹ)) (sym aux) · sym (Π[]ᴹ (ty A) (ty B) (tms σ)))) ⟩
      (tm (subst (Tm _) (sym (Π[] A B σ)) (lam (t [ σ ↑ A ]'))))
        ∎
      where
        _↑ᴹ_ : ∀{Γ Δ} → (σ : Tmsᴹ Γ Δ) → (A : Tyᴹ Δ) → Tmsᴹ (Γ ,ᴹ (A [ σ ]ᴹ)) (Δ ,ᴹ A)
        σ ↑ᴹ A = (σ ∘ᴹ π₁ᴹ (idᴹ _)) ,sᴹ subst (Tmᴹ _) [][]ᴹ (π₂ᴹ (idᴹ (_ ,ᴹ (A [ σ ]ᴹ))))
        aux : tms σ ↑ᴹ ty A ≡ tms (σ ↑ A)
        aux = ap (tms (σ ∘ π₁ (id (Γ , (A [ σ ])))) ,sᴹ_) (sym (swap-subst {t = π₂ (id (_ , (A [ σ ])))} [][] [][]ᴹ))
