{-# OPTIONS --allow-unsolved-metas #-}

module Utils where

open import Function using (_$_ ; _∘_ ; id)
open import Cubical.Core.Prelude
open import Cubical.Core.Glue -- Basics.Everything
open import Cubical.Basics.Everything

-- uncurry : ∀{l l' l''} {A : Set l} {B : Set l'} {C : Set l''}
--         -> (A -> B -> C) -> A × B -> C
-- uncurry f (x , y) = f x y

subst2 : {ℓ ℓ' l : Level} {A : Set ℓ} {B : Set l} (C : A -> B → Set ℓ')
      {a a' : A} {b b' : B} →
      a ≡ a' -> b ≡ b' → C a b → C a' b'
subst2 C p q x = subst (λ y → C y _) p (subst (C _) q x)

infixl 6 _·_
_·_ = compPath

ap = cong

cong2 : ∀{ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
      {x y : A} {z w : B} (f : A → B → C) (p : x ≡ y) (q : z ≡ w)
      → f x z ≡ f y w
cong2 = {!!}

module _ {l l'} {A : Set l} {B : Set l'} (f : A -> B) where

  qinv : Set _
  qinv = Σ (B -> A) λ g → (f ∘ g ≡ id) × (g ∘ f ≡ id)

  qinvIsEquiv : qinv -> isEquiv f
  qinvIsEquiv q =
    isoToIsEquiv f (fst q) (λ y → cong (_$ y) $ fst (snd q))
                           (λ x → cong (_$ x) $ snd (snd q))

module _ {l l'} {A : Set l} {B : A -> Set l'} where

  module _ {p q : Σ A B} where

    Σ-≡ : Σ (fst p ≡ fst q) (λ r → subst B r (snd p) ≡ snd q) → p ≡ q
    Σ-≡ (h1 , h2) =
      compPath (J (λ q1' k' → (p1 , p2) ≡ (q1' , subst B k' p2))
                  (cong {_} {B p1} {_} {λ _ → Σ A B} {p2} {subst B refl p2} (p1 ,_)
                    (sym (substRefl B p2))) h1)
               (cong (λ x → (q1 , x)) h2)
      where p1 = fst p ; p2 = snd p ; q1 = fst q

    coΣ-≡ : p ≡ q → Σ (fst p ≡ fst q) (λ r → subst B r (snd p) ≡ snd q)
    coΣ-≡ eq = J {A = Σ A B} {p} (λ q' eq' → Σ _ (λ r → subst _ r (snd p) ≡ snd q'))
                    (refl , (transpRefl _ (snd p))) eq
      
  Σiso1 : {p1 q1 : A} (r : p1 ≡ q1) {p2 : B p1} {q2 : B q1} (k : subst B r p2 ≡ q2)
        -> coΣ-≡ (Σ-≡ (r , k)) ≡ (r , k)
  Σiso1 {p1} {q1} r =
    J (λ q1' r' → ({p2 : B p1} {q2 : B q1'} (k : subst B r' p2 ≡ q2)
        -> coΣ-≡ (Σ-≡ (r' , k)) ≡ (r' , k))) (λ k → {!!}) r

  module _ {p q : Σ A B} where

    coΣ-≡-qinv : qinv coΣ-≡
    coΣ-≡-qinv = Σ-≡ , (funExt _ (λ x → Σiso1 (fst x) (snd x)) , {!!})

    Σ-≡-equiv : (p ≡ q) ≃ Σ (fst p ≡ fst q) (λ r → subst B r (snd p) ≡ snd q)
    Σ-≡-equiv = coΣ-≡ , qinvIsEquiv coΣ-≡ coΣ-≡-qinv
      where p1 = fst p ; p2 = snd p ; q1 = fst q

module _ {l l'} {A : Set l} {B : Set l'} where

  ×-≡ : {p q : A × B} -> fst p ≡ fst q -> snd p ≡ snd q -> p ≡ q
  ×-≡ {p} h1 h2 = Σ-≡ (h1 , transpRefl B (snd p) · h2)

×-prop : ∀{l l'} {P : Set l} {Q : Set l'}
       -> isProp P -> isProp Q -> isProp (P × Q)
×-prop p q x y = Σ-≡ (p _ _ , q _ _)

Π-prop :  ∀{l l'} {A : Set l} {B : A -> Set l'}
       -> ((x : A) -> isProp (B x)) -> isProp ((x : A) -> B x)
Π-prop h f g = funExt _ (λ x → h x _ _)

funExt' : {ℓ ℓ' : Level} {A : Set ℓ} (B : A → Set ℓ')
      {f g : {x : A} → B x} →
      ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g
funExt' B {f} {g} h i {x} = h x i

Σ-prop-≡ : ∀{l l'} {A : Set l} {P : A → Set l'} {p q : Σ A P}
         → ((x : A) → isProp (P x))
         → fst p ≡ fst q
         → p ≡ q
Σ-prop-≡ h prf = Σ-≡ (prf , h _ _ _)

-- Σ-sub-isset : ∀{l l'} {A : Set l} {P : A → Set l'} {p q : Σ A P}
--            -> isSet A 
--            -> ((x : A) → isProp (P x))
--            -> (p ≡ q) ≃ (fst p ≡ fst q)
-- Σ-sub-isset {p = p} {q} ss pp =
--   isoToEquiv (cong fst) (Σ-prop-≡ pp)
--     (λ r → ss (fst p) (fst q) _ r)
--     (λ s → {!!})

h-level : ∀{l} → ℕ → Set l → Set l
h-level zero A = isContr A
h-level (suc n) A = (x y : A) → h-level n (x ≡ y)

h-lev-equiv : ∀{l} {A B : Set l} -> A ≃ B
            -> (n : ℕ) -> h-level n A -> h-level n B
h-lev-equiv eqv n h = subst (h-level n) (ua eqv) h

postulate
  propIsSet : ∀{l} (P : Set l) -> isProp P -> isSet P

Σ-level : ∀{l l'} {A : Set l} {B : A -> Set l'}
       -> (n : ℕ)
       -> h-level n A
       -> ((x : A) -> h-level n (B x))
       -> h-level n (Σ A B)
Σ-level zero h1 h2 = (fst h1 , fst (h2 _)) , λ { (x , y) →
  Σ-≡ (snd h1 x , (sym $ snd (h2 x) (subst _ (snd h1 x) (fst (h2 (fst h1)))))
                       · snd (h2 x) y) }
Σ-level (suc n) h1 h2 (a1 , b1) (a2 , b2) =
  h-lev-equiv (invEquiv Σ-≡-equiv) n (Σ-level n (h1 a1 a2) λ x → h2 _ _ _)

Π-level : ∀{l l'} {A : Set l} {B : A -> Set l'}
       -> (n : ℕ)
       -> ((x : A) -> h-level n (B x))
       -> h-level n ((x : A) -> B x)
Π-level zero h = (λ x → fst (h x)) , λ y → funExt _ (λ x → snd (h x) (y x))
Π-level (suc n) h f g = {!!}

_∼_ : ∀{l l'} {A : Set l} {B : A -> Set l'} (f g : (x : A) -> B x) -> Set _
f ∼ g = ((x : _) -> f x ≡ g x)

open import Function

funExt≃ : ∀{l l'} {A : Set l} {B : A -> Set l'} {f g : (x : A) -> B x}
       -> (f ≡ g) ≃ (f ∼ g)
funExt≃ = isoToEquiv (λ p → λ x → cong (_$ x) p) (funExt _)
  (λ h → funExt _ (λ x → {!!})) λ x → {!!}

Π-set : ∀{l l'} {A : Set l} {B : A -> Set l'}
     -> ((x : A) -> isSet (B x))
     -> isSet ((x : A) -> B x)
Π-set h f g p q = {!!}

module _ {l} where
  postulate
    ·refl : {A : Set l} {x y : A} → (p : x ≡ y) → p · refl ≡ p
    refl· : {A : Set l} {x y : A} → (p : x ≡ y) → refl · p ≡ p
    assoc : {A : Set l} {x y z w : A} → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
          → (p · q) · r ≡ p · (q · r)

  inv : {A : Set l} {x y : A} → (p : x ≡ y) → sym p · p ≡ refl
  inv = J (λ y r → sym r · r ≡ refl) (·refl refl)

hlev-upw : ∀{l} {n : ℕ} {A : Set l} → h-level n A → h-level (suc n) A
hlev-upw {n = zero} h a b = p b , hh b
  where
    p : (y : _) → a ≡ y
    p y = sym (snd h a) · snd h y
    hh : (y : _) → (q : a ≡ y) → p y ≡ q
    hh y = J {x = a} (λ y q → p y ≡ q) (inv (snd h a))
hlev-upw {n = suc n} h x y p q = hlev-upw {n = n} (h _ _) p q

Σ-set : ∀{l l'} {A : Set l} {B : A -> Set l'}
       -- -> (n : ℕ)
       -> isSet A -> ((x : A) -> isSet (B x))
       -> isSet (Σ A B)
Σ-set n = {!!}

Σ-subset : ∀{l l'} {A : Set l} {P : A → Set l'}
           -> isSet A 
           -> ((x : A) → isProp (P x))
           -> isSet (Σ A P)
Σ-subset ss pp = Σ-set ss (λ x → {!!})

≡-on-≃ : ∀{l} {A : Set l} {B : Set l} {x y : A}
      -> (eq : A ≃ B) -> fst eq x ≡ fst eq y -> x ≡ y
≡-on-≃ {x = x} {y} eq p = sym (secEq eq x) · cong (invEq eq) p · secEq eq y

module _ {l} where
  record ⊤ : Set l where constructor tt

  ⊤-is-contr : isContr ⊤
  ⊤-is-contr = tt , λ _ → refl

  ⊤-is-set : isSet ⊤
  ⊤-is-set = λ x y p q → fst (aux x y p q)
    where aux = hlev-upw (hlev-upw ⊤-is-contr)

postulate
--   ∼≃≡ : ∀{l l'} {A : Set l} {B : A → Set l'}
--     → {f g : (a : A) → B a}
--     → (f ∼ g) ≡ (f ≡ g)
    
  →-set : ∀{l} → {A B : Set l} → isSet A → isSet B → isSet (A → B)
-- →-set a b = λ f g p q → {!∼≃≡ !}

-- data ∥_∥ {l} (A : Set l) : Set l where
--   ∣_∣ : A → ∥ A ∥
--   trunc : (x y : A) → ∣ x ∣ ≡ ∣ y ∣

-- join : ∀{l} {A : Set l} → ∥ ∥ A ∥ ∥ → ∥ A ∥
-- join ∣ x ∣ = x
-- join (trunc x y i) = {!!}

-- _>>=_ : ∀{l l'} {A : Set l} {B : Set l'} → ∥ A ∥ → (A → ∥ B ∥) → ∥ B ∥
-- ∣ x ∣ >>= f = f x
-- trunc x y i >>= f = {!trunc (f x) (f y) i!}
