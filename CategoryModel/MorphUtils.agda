{-# OPTIONS --allow-unsolved-metas #-}

module CategoryModel.MorphUtils where

open import CategoryTheory
open import Cubical.Core.Prelude
open import Utils renaming (_·_ to _▪_)
open import Agda.Primitive

module MU {l l'} (C : Category {l} {l'}) where

  open Category C
  open Functor

  substMorph : {a b c : Category.Obj C}
             -> a ≡ b -> Morph a c -> Morph b c
  substMorph p u = subst (λ z → Morph z _) p u

  substMorph2 : ∀{a b c d} -> a ≡ c -> b ≡ d -> Morph a b -> Morph c d
  substMorph2 {a} {b} {_} {d} =
    J (λ c' p' → b ≡ d -> Morph a b -> Morph c' d)
      (J (λ d' q' → Morph a b -> Morph a d') λ x → x)

  substMorph2-refl : ∀{a b} (m : Morph a b) -> substMorph2 refl refl m ≡ m
  substMorph2-refl m = transpRefl _ _ ▪ {!!}

  substMorph∘ : ∀{a b c d} (p : a ≡ b) (m : Morph a c) (m' : Morph c d)
              -> m' ∘ (substMorph p m) ≡ substMorph p (m' ∘ m)
  substMorph∘ {a} {_} {c} {d} = J (λ b' p' → (m : Morph a c) (m' : Morph c d)
              -> m' ∘ (substMorph p' m) ≡ substMorph p' (m' ∘ m))
              λ m m' → ap (m' ∘_) (transpRefl _ m) ▪ sym (transpRefl _ _)

  substMorph2∘ : ∀{a a' b b' c} (p : a ≡ a') (q : b ≡ b') (m : Morph a b) (m' : Morph b c)
               -> substMorph q m' ∘ substMorph2 p q m ≡ substMorph p (m' ∘ m)
  substMorph2∘ = J (λ a'' p' → (q : _ ≡ _) (m : Morph _ _) (m' : Morph _ _)
               -> substMorph q m' ∘ substMorph2 p' q m ≡ substMorph p' (m' ∘ m))
                 (J (λ b'' q' → (m : Morph _ _) (m' : Morph _ _)
               -> substMorph q' m' ∘ substMorph2 refl q' m ≡ substMorph refl (m' ∘ m))
                 λ m m' → ap (substMorph refl m' ∘_) (substMorph2-refl m)
                        ▪ (ap (_∘ m) (transpRefl _ _) ▪ sym (transpRefl _ _)))
  
  joinSM-2 : ∀{a b c e} (p : a ≡ b) (q : b ≡ c) (m : Morph a e)
         -> substMorph q (substMorph p m) ≡ substMorph (p ▪ q) m
  joinSM-2 = {!!}

  joinSM : ∀{a b c d e} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (m : Morph a e)
         -> substMorph r (substMorph q (substMorph p m)) ≡ substMorph (p ▪ q ▪ r) m
  joinSM p q r m = {!!}

  remove-SM : ∀{a b} -> isSet Obj -> (p : a ≡ a) (m : Morph a b)
            -> substMorph p m ≡ m
  remove-SM {a} h p m = K h a (λ p' → substMorph p' m ≡ m) (transpRefl _ _) p

  substMorphR : {a b c : Category.Obj C}
           -> b ≡ c -> Morph a b -> Morph a c
  substMorphR p u = subst (Morph _) p u

  substMorphL-irrel : ∀{a b c} {p q : a ≡ b} (m : Morph a c)
                    -> p ≡ q -> substMorph p m ≡ substMorph q m
  substMorphL-irrel = {!!}

  substMorphR-irrel : ∀{a b c} {p q : b ≡ c} (m : Morph a b)
                    -> p ≡ q -> substMorphR p m ≡ substMorphR q m
  substMorphR-irrel = {!!}

  remove-SMR : ∀{a b} -> isSet Obj -> (p : a ≡ a) (m : Morph b a)
            -> substMorphR p m ≡ m
  remove-SMR {a} h p m = {!!} -- K h a (λ p' → substMorph p' m ≡ m) (transpRefl _ _) p

  joinSMR-2 : ∀{a b c e} (p : a ≡ b) (q : b ≡ c) (m : Morph e a)
         -> substMorphR q (substMorphR p m) ≡ substMorphR (p ▪ q) m
  joinSMR-2 p q m = {!!}

  joinSMR-3 : ∀{a b c d e} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) (m : Morph e a)
         -> substMorphR r (substMorphR q (substMorphR p m)) ≡ substMorphR (p ▪ q ▪ r) m
  joinSMR-3 p q r m = {!!}

  substMorphR∘ : ∀{a b c d} (p : c ≡ d) (m : Morph a b) (m' : Morph b c)
               -> substMorphR p m' ∘ m ≡ substMorphR p (m' ∘ m)
  substMorphR∘ = {!!}

  substMorph2∘' : ∀{a b b' c c'} (p : b ≡ b') (q : c ≡ c') (m : Morph a b) (m' : Morph b c)
                -> substMorph2 p q m' ∘ substMorphR p m ≡ substMorphR q (m' ∘ m)
  substMorph2∘' p q m m' = {!!}

module _ {l} {l'} {l''} {l'''}
  {C : Category {l} {l'}}
  {D : Category {l''} {l'''}}
  (F : C ⟶ D) where

  open Category
  open Functor

  Fcomm-SM : {a b c : _} (p : a ≡ b) (m : Morph C a c)
           -> (F ₁) (MU.substMorph C p m) ≡ MU.substMorph D (ap (F ₀) p) ((F ₁) m)
  Fcomm-SM = J (λ b' p' → (m : Morph C _ _)
                  -> (F ₁) (MU.substMorph C p' m) ≡ MU.substMorph D (ap (F ₀) p') ((F ₁) m))
                     λ m → ap (F ₁) (transpRefl _ m) ▪ sym (transpRefl _ _)

  fid-SM : {x y : _} (p : x ≡ y)
         -> (F ₁) (MU.substMorph C p (id C x))
          ≡ MU.substMorph D (ap (F ₀) p) (id D ((F ₀) x))
  fid-SM {x} = J (λ y' p' → (F ₁) (MU.substMorph C p' (id C x))
             ≡ MU.substMorph D (ap (F ₀) p') (id D ((F ₀) x)))
               (ap (F ₁) (transpRefl (Morph C x x) (id C x))
             ▪ fid F x ▪ sym {!!})

open import Function using (_$_)


module _ {l} {C D : Category {l} {l}} {F G : Functor C D} where
  open Category
  open Functor

  onF≡ : F ≡ G -> FunctorEq C D (F ₀) (λ a b → F ₁) (G ₀) (λ a b → G ₁)
  onF≡ = J (λ G' p' → FunctorEq C D (F ₀) (λ a b → F ₁) (G' ₀) (λ a b → G' ₁))
           (FunctorEq-refl F)

module TyUtils {l} (strct : (C : Category {l} {l}) → isStrictCategory C) where

  open CatCategory strct
  open Category
  open Functor

  module _ {C : Category {l} {l}} (F : C ⟶ Cat) where

    private
      idC = id C

      infixr 6 _·_
      _·_ : ∀{γ γ'} -> Morph C γ γ' -> Obj ((F ₀) γ) -> Obj ((F ₀) γ')
      p · a = ((F ₁) p ₀) a

    asder : ∀{a b b' c}
          -> (p : Morph C a b) (q : Morph C b c)
          -> (p' : Morph C a b') (q' : Morph C b' c)
          -> (x : Obj ((F ₀) a))
          -> _∘_ C q p ≡ _∘_ C q' p'
          -> (((F ₁) q) ₀) ((((F ₁) p) ₀) x) ≡ (((F ₁) q') ₀) ((((F ₁) p') ₀) x)
    asder p q p' q' x h =
        ap (_$ x) (ap _₀ (sym (f∘ F q p)))
      ▪ ap (λ z → (((F ₁) z) ₀) x) h
      ▪ ap (_$ x) (ap _₀ (f∘ F q' p'))

    module _ {γ} where

      open MU ((F ₀) γ)
  
      overFid-prf : ∀ a -> a ≡ idC γ · a
      overFid-prf a = sym (ap (_$ a) $ ap _₀ $ fid F γ)

      overFidL : ∀{a b} -> Morph ((F ₀) γ) a b -> Morph ((F ₀) γ) (idC γ · a) b
      overFidL {a} = substMorph (overFid-prf a)

      overFidR : ∀{a b} -> Morph ((F ₀) γ) a b -> Morph ((F ₀) γ) a (idC γ · b)
      overFidR {_} {b} = substMorphR (overFid-prf b)

      IdFun-lemma : ∀{a b} (m : Morph ((F ₀) γ) a b)
                  -> ((F ₁) (idC γ) ₁) m
                  ≡ MU.substMorph2 ((F ₀) γ) (overFid-prf a) (overFid-prf b) m
      IdFun-lemma {a} {b} m = {!eq1 (onF≡ (fid F γ)) m!}
        where open FunctorEq
        
    module _ {γ γ' γ''} (p : Morph C γ γ') (p' : Morph C γ' γ'') where

      open MU ((F ₀) γ'')

      overF∘-prf : ∀ x -> p' · p · x ≡ _∘_ C p' p · x
      overF∘-prf x = sym (ap (_$ x) $ ap _₀ $ f∘ F p' p)

      overF∘L : {x : _} {y : _}
              -> Morph ((F ₀) γ'') (p' · p · x) y
              -> Morph ((F ₀) γ'') (_∘_ C p' p · x) y
      overF∘L {x} = substMorph (overF∘-prf x)

      overF∘R : {x : _} {y : _}
              -> Morph ((F ₀) γ'') x (p' · p · y)
              -> Morph ((F ₀) γ'') x (_∘_ C p' p · y)
      overF∘R {_} {y} = substMorphR (overF∘-prf y)

    module _ {γ γ' γ''} (p : Morph C γ γ') (p' : Morph C γ' γ'') where

      open MU ((F ₀) γ'')

      overF∘L-comp : {x : _} {y z : _}
                    (m : Morph ((F ₀) γ'') (p' · p · x) y)
                    (m' : Morph ((F ₀) γ'') y z)
                  -> _∘_ ((F ₀) γ'') m' (overF∘L p p' m) ≡ overF∘L p p' (_∘_ ((F ₀) γ'') m' m)
      overF∘L-comp m m' = substMorph∘ _ m m'

      overF∘R-comp : {x : _} {y : _} {z : _}
                    (m : Morph ((F ₀) γ'') z x)
                    (m' : Morph ((F ₀) γ'') x (p' · p · y))
                  -> _∘_ ((F ₀) γ'') (overF∘R p p' m') m ≡ overF∘R p p' (_∘_ ((F ₀) γ'') m' m)
      overF∘R-comp m m' = substMorphR∘ _ m m'
