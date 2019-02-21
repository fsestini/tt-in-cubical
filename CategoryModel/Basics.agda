{-# OPTIONS --allow-unsolved-metas #-}

module CategoryModel.Basics {l} where

open import Function using (_$_)
open import Cubical.Core.Prelude
open import CategoryTheory
open import Utils
open import Agda.Primitive
open import CategoryModel.MorphUtils

-- we work exclusively with strict categories everywhere
postulate
  strct : (C : Category {l} {l}) -> isStrictCategory C

open CatCategory strct
open TyUtils strct

Ty : Category {l} {l} -> Set (lsuc l)
Ty Γ = Γ ⟶ Cat

ty-op : {Γ : Category} -> Ty Γ -> Ty Γ
ty-op A = compFun A op-functor

module _ {Γ : Category {l} {l}} (A : Ty Γ) where

  open Category
  open Functor

  -- overFid-commute : ∀{γ γ'} {x : _} (p : Morph Γ γ γ')
  --                 -> (((A ₁) p ₁) (overFid (id ((A ₀) γ) x)))
  --                  ≡ MU.substMorph ((A ₀) γ')
  --                         (sym {!!}) (id ((A ₀) γ') ((A ₁) p ₀ $ x))
  -- overFid-commute p = {!!}

  -- overFid-lemma : ∀{γ γ'} {x : _} {x' : _}
  --               -> (p : Morph Γ γ γ') (q : Morph ((A ₀) γ') (((A ₁) p ₀) x) x')
  --               -> _∘_ ((A ₀) γ') (overFidL A (id ((A ₀) γ') x')) ((((A ₁) (id Γ _)) ₁) q) ≡ overFidL A q
  -- overFid-lemma {γ} {γ'} {x} {x'} p q = begin
  --   _
  --     ≡⟨ ap (λ z → _∘_ ((A ₀) γ') (overFidL A (id ((A ₀) γ') x')) z) (IdFun-lemma {Γ} A q) ⟩
  --   _∘_ ((A ₀) γ') (overFidL A (id ((A ₀) γ') x')) (MU.substMorph2 ((A ₀) γ') (sym (fid-prf A _)) (sym (fid-prf A x')) q)
  --     ≡⟨ MU.substMorph2∘ ((A ₀) γ') (sym (fid-prf A _)) (sym (fid-prf A x')) q (id ((A ₀) γ') x') ⟩
  --   overFidL A (_∘_ ((A ₀) γ') (id ((A ₀) γ') x') q)
  --     ≡⟨ ap (overFidL A) (id∘ ((A ₀) γ') q) ⟩
  --   overFidL A q
  --     ∎

open Category
open Functor

_,,_ : (Γ : Category) -> Ty Γ -> Category {l} {l}
Obj (Γ ,, A) = Σ (Obj Γ) λ γ → Obj ((A ₀) γ)
Morph (Γ ,, A) (γ , x) (γ' , x') =
  Σ (Morph Γ γ γ') λ p → Morph ((A ₀) γ') ((((A ₁) p) ₀) x) x'
id (Γ ,, A) (γ , x) = id Γ γ , overFidL A (id ((A ₀) γ) x)
_∘_ (Γ ,, A) {γ , x} {γ' , x'} {γ'' , x''} (p' , q') (p , q) =
  _∘_ Γ p' p , _∘_ ((A ₀) γ'') q' (overF∘L A p p' ((((A ₁) p') ₁) q))
hom-set (Γ ,, A) {b = b} = Σ-set (hom-set Γ) λ x → hom-set ((A ₀) (fst b))
id∘ (Γ ,, A) {γ , x} {γ' , x'} (p , q) = Σ-≡ (id∘ Γ p , goal)
  where
    open MU ((A ₀) γ')
    sub = substMorph (ap (λ z → ((A ₁) z) ₀ $ x) (id∘ Γ p))
    goal = begin
      _ ≡⟨ ap sub (overF∘L-comp A p (id Γ γ') _ _) ⟩
      sub (overF∘L A p (id Γ γ') (_∘_ ((A ₀) γ') (overFidL A (id ((A ₀) γ') x')) (((A ₁) (id Γ γ') ₁) q)))
        ≡⟨ {!!} -- ap (λ z → sub (overF∘L A p (id Γ γ') z)) (overFid-lemma {Γ} A p q)
          ⟩
      sub (overF∘L A p (id Γ γ') (overFidL A q)) 
        ≡⟨ joinSM _ _ _ q ⟩
      _ ≡⟨ remove-SM {!!} _ _ ⟩
      _ ∎
∘id (Γ ,, A) {γ , x} {γ' , x'} (p , q) = Σ-≡ (∘id Γ p , goal)
  where
    open MU ((A ₀) γ')
    sub = substMorph (ap (λ z → ((A ₁) z) ₀ $ x) (∘id Γ p))
    goal = begin
      _ ≡⟨ ap sub (overF∘L-comp A (id Γ γ) p (((A ₁) p ₁)
                                    (overFidL A (id ((A ₀) γ) x))) q) ⟩
      _ ≡⟨ ap (λ z → sub (overF∘L A (id Γ γ) p (_∘_ ((A ₀) γ') q z)))
                       (fid-SM ((A ₁) p) _) ⟩
      _ ≡⟨ ap (λ z → sub (overF∘L A (id Γ γ) p z)) (substMorph∘ _ _ q) ⟩
      _ ≡⟨ joinSM _ _ _ (_∘_ ((A ₀) γ') q (id (A ₀ $ γ') ((A ₁) p ₀ $ x))) ⟩
      _ ≡⟨ remove-SM {!!} _ _ ⟩
      _ ≡⟨ ∘id ((A ₀) γ') q ⟩
      _ ∎
∘∘ (Γ ,, A) = {!!}

_,,op_ : (Γ : Category) -> Ty (Γ ᵒᵖ) -> Category {l} {l}
Obj (Γ ,,op A) = Σ (Obj Γ) λ γ → Obj ((A ₀) γ)
Morph (Γ ,,op A) (γ , x) (γ' , x') = Σ (Morph Γ γ γ') λ f → Morph ((A ₀) γ) x ((((A ₁) f) ₀) x')
id (Γ ,,op A) (γ , x) = id Γ γ , overFidR A (id ((A ₀) γ) x)
_∘_ (Γ ,,op A) {γ , x} {γ' , x'} {γ'' , x''} (p' , q') (p , q)
  = _∘_ Γ p' p , _∘_ ((A ₀) γ) (overF∘R A p' p (((A ₁) p ₁) q')) q
id∘ (Γ ,,op A) (p , q) = Σ-≡ (id∘ Γ p , {!!})
∘id (Γ ,,op A) = {!!}
∘∘ (Γ ,,op A) = {!!}
hom-set (Γ ,,op A) = {!!}

module _ {Γ : Category} (A : Ty (Γ ᵒᵖ)) {γ γ'} {a a' : Obj ((A ₀) γ')}
           (p : Morph Γ γ γ') (q : Morph (A ₀ $ γ') a a') where
  
  private
    p·a = (((A ₁) p) ₀ $ a)
    p·a' = (((A ₁) p) ₀ $ a')
    p·q = ((A ₁) p) ₁ $ q

  p-id-q-lemma : (_∘_ (Γ ,,op A) (p , id ((A ₀) γ) p·a') (id Γ γ , overFidR A p·q))
               ≡ (p , p·q)
  p-id-q-lemma = Σ-≡ (∘id Γ p , goal)
    where
      sub = MU.substMorphR ((A ₀) γ) (ap (λ f → (f ₀) a') (ap (A ₁) (∘id Γ p)))
      goal = begin
        _ ≡⟨ ap sub (MU.substMorphR∘ ((A ₀) γ) _ (overFidR A p·q) (((A ₁) (id Γ γ) ₁) (id ((A ₀) γ) p·a'))) ⟩
        _ ≡⟨ ap sub (ap (overF∘R A p (id Γ γ)) (ap (λ z → _∘_ ((A ₀) γ) z (overFidR A p·q)) (IdFun-lemma A _))) ⟩
        _ ≡⟨ ap sub (ap (overF∘R A p (id Γ γ)) (MU.substMorph2∘' ((A ₀) γ) _ _ _ _)) ⟩
        _ ≡⟨ ap sub (ap (overF∘R A p (id Γ γ)) (ap (MU.substMorphR ((A ₀) γ) _) (id∘ ((A ₀) γ) p·q))) ⟩
        _ ≡⟨ MU.joinSMR-3 ((A ₀) γ) _ _ _ p·q ⟩
        _ ≡⟨ MU.remove-SMR ((A ₀) γ) (λ x y → strct ((A ₀) γ)) _ _ ⟩
        _ ∎

  p-id-q-lemma' : (_∘_ (Γ ,,op A) (id Γ γ' , overFidR A q) (p , (id ((A ₀) γ) p·a)))
                ≡ (p , p·q)
  p-id-q-lemma' = Σ-≡ (id∘ Γ p , {!!})

module _ where

  open Category
  open Functor

  record Tm (Γ : Category) (A : Ty Γ) : Set l where
    field
      _₀' : (γ : Obj Γ) → Obj ((A ₀) γ)
      _₁' : ∀{γ γ'} → (p : Morph Γ γ γ')
                    → Morph ((A ₀) γ') (((A ₁) p ₀) (_₀' γ)) (_₀' γ')
      fid' : ∀ γ → _₁' (id Γ γ) ≡ overFidL A (id ((A ₀) γ) (_₀' γ))
      f∘'  : ∀{γ γ' γ''} → (p : Morph Γ γ γ') (p' : Morph Γ γ' γ'')
           -> _₁' (_∘_ Γ p' p) ≡ overF∘L A p p' (_∘_ ((A ₀) γ'')
                                                       (_₁' p')
                                                       (((A ₁) p' ₁) (_₁' p)))

  open Tm

  module _ {Γ} {A : Ty Γ} where

    _◂ : Tm Γ A → Γ ⟶ (Γ ,, A)
    (M ◂ ₀) γ = γ , (M ₀') γ
    (M ◂ ₁) p = p , (M ₁') p
    fid (M ◂) x = Σ-≡ (refl , transpRefl _ _ · fid' M x)
    f∘ (M ◂) f g = Σ-≡ (refl , (transpRefl _ _ · (f∘' M g f
                                               · sym (overF∘L-comp A _ _ _ _))))

    record TmMorph (M N : Tm Γ A) : Set l where
      -- no-eta-equality
      constructor MkTmMorph
      field
        morph : (γ : Obj Γ) -> Morph ((A ₀) γ) ((M ₀') γ) ((N ₀') γ)
        natural : isNatural _ _ (M ◂) (N ◂) (λ γ → id Γ _ , overFidL A (morph γ))
    open TmMorph

    postulate
      TmMorphEq : {M N : Tm Γ A} {f g : TmMorph M N}
                -> morph f ≡ morph g -> f ≡ g
    -- TmMorphEq {M} {N} {f} {g} h = {!!}

  open TmMorph

  Tmᶜ : (Γ : Category) (A : Ty Γ) -> Category
  Obj (Tmᶜ Γ A) = Tm Γ A
  Morph (Tmᶜ Γ A) M N = TmMorph M N
  id (Tmᶜ Γ A) M = MkTmMorph (λ γ → id ((A ₀) γ) ((M ₀') γ)) λ {γ} {γ'} f →
    let τ = λ γ → id ((A ₀) γ) ((M ₀') γ)
        goal = ap ((A ₀) γ' ∘ (M ₁') f) (fid ((A ₁) f) ((M ₀') γ))
             · ∘id ((A ₀) γ') _ · sym (id∘ ((A ₀) γ') _)
        sub = MU.substMorph ((A ₀) γ')
                  (ap (_$ _) $ ap _₀ $ ap (A ₁) (∘id Γ f · sym (id∘ Γ f)))
        goal' = begin
          _ ≡⟨ ap sub (ap (_∘_ ((A ₀) γ') ((M ₁') f)) (ap (overF∘L A (id Γ γ) f)
                  (Fcomm-SM ((A ₁) f) (overFid-prf A _) (τ γ)))) ⟩
          _ ≡⟨ ap sub (ap ((A ₀) γ' ∘ _)
                 (MU.joinSM-2 ((A ₀) γ') _ _ (((A ₁) f) ₁ $ (τ γ)))) ⟩
          _ ≡⟨ ap sub (MU.substMorph∘ ((A ₀) γ') _ _ _) ⟩
          _ ≡⟨ MU.joinSM-2 ((A ₀) γ') _ _ (_∘_ ((A ₀) γ') ((M ₁') f) (((A ₁) f) ₁ $ (τ γ))) ⟩
          _ ≡⟨ MU.substMorphL-irrel ((A ₀) γ') _ (strct ((A ₀) γ') _ _) ⟩
          _ ≡⟨ ap (MU.substMorph ((A ₀) γ') _) goal ⟩
          _ ≡⟨ sym (MU.joinSM-2 ((A ₀) γ') _ _ _) ⟩
          _ ≡⟨ ap (overF∘L A f (id Γ γ')) (sym (MU.substMorph2∘ ((A ₀) γ') _ _ _ _)) ⟩
          _ ≡⟨ ap (overF∘L A f (id Γ γ')) (ap ((A ₀) γ' ∘ overFidL A (τ γ'))
                 (sym (IdFun-lemma A ((M ₁') f)))) ⟩
          _ ≡⟨ sym (MU.substMorph∘ ((A ₀) γ') _ _ _) ⟩
          _ ∎
    in Σ-≡ (∘id Γ f · sym (id∘ Γ f) , goal')

  _∘_ (Tmᶜ Γ A) M N =
    MkTmMorph (λ γ → _∘_ ((A ₀) γ) (morph M γ) (morph N γ)) {!!}
  hom-set (Tmᶜ Γ A) = {!!}
  id∘ (Tmᶜ Γ A) f = TmMorphEq (funExt _ (λ x → id∘ ((A ₀) x) (morph f x)))
  ∘id (Tmᶜ Γ A) f = TmMorphEq (funExt _ (λ x → ∘id ((A ₀) x) (morph f x)))
  ∘∘ (Tmᶜ Γ A) f g h =
    TmMorphEq (funExt _ (λ x → ∘∘ ((A ₀) x) (morph f x) (morph g x) (morph h x)))
