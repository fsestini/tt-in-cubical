module GroupoidModel.IdTypes {l} where

open import Cubical.Core.Prelude
open import CategoryTheory
open import GroupoidModel.Groupoid
open import GroupoidModel.Basics
open import GroupoidModel.Universe {l}
open import Agda.Primitive
open import Function using (_$_)
open import Utils

open Groupoid

module _ (A : Groupoid {l}) where

  open Functor

  Id : Functor (cat (gcross A A)) (cat Gpd)
  (Id ₀) (a₁ , a₂) = Δgrpd (Morph a₁ a₂) hom-set
    where open Category (cat A)
  (Id ₁) {a = a1 , a2} {b = b1 , b2} (p1 , p2) =
    (MkFunctor' (MkFunct (λ q → p2 ∘ (q ∘ fst (grpd A p1)))
                         (ap (λ a → p2 ∘ (a ∘ fst (grpd A p1))))
                         (λ x → hom-set _ _ _ _) λ f g → hom-set _ _ _ _)) ,
    (MkFunctor' (MkFunct (λ q → fst (grpd A p2) ∘ (q ∘ p1))
                         (ap (λ a → fst (grpd A p2) ∘ (a ∘ p1)))
                         (λ x → hom-set _ _ _ _) λ f g → hom-set _ _ _ _))
    , {!!}
    where open Category (cat A)
  fid Id = {!!}
  f∘ Id = {!!}

  IdTy : Ty (gcross A A)
  IdTy = compFun _ _ _ Id incl

  dupl : Functor (cat A) (cross (cat A) (cat A))
  (dupl ₀) x = x , x
  (dupl ₁) f = f , f
  fid dupl = {!!}
  f∘ dupl = {!!}

  open Tm
  open import Utils

  refl-ctor : Tm A (compFun _ _ _ dupl IdTy)
  (refl-ctor ₀') a = gid A a
  (refl-ctor ₁') p = ap (p ∘_) (id∘ _) · snd (snd (grpd A p))
    where open Category (cat A)
  fid' refl-ctor _ = {!!}
    where open Category (cat A)
  f∘' refl-ctor _ _ = {!!}

  refl-fun : Functor (cat A) (cat (gcross A A ,, IdTy))
  (refl-fun ₀) x = (x , x) , (refl-ctor ₀' $ x)
  (refl-fun ₁) f = (f , f) , (refl-ctor ₁' $ f)

  module _ (C : Functor (cat (gcross A A ,, IdTy)) (cat Gpd))
           (h : Tm A (compFun _ _ _ refl-fun (compFun _ _ _ C incl))) where

    open Functor'
    -- open Category

    J-elim : Tm (gcross A A ,, IdTy) (compFun _ _ _ C incl)
    (J-elim ₀') ((a1 , a2) , r) =
      (unFunctor' $ fst ((C ₁) (((gid A a1) , r) , aux))) ₀ $ h ₀' $ a1
      where
        open Category (cat A)
        aux : (r ∘ (id a1 ∘ fst (grpd A (id a1)))) ≡ r
        aux = ap (r ∘_) (snd (snd (grpd A (id a1)))) · ∘id r
    (J-elim ₁') {(a1 , a2) , r} {(a1' , a2') , r'} ((p₁ , p₂) , q) = goal
      where
        open Category
        
        C1 : ∀{a b} -> Morph (cat (gcross A A ,, IdTy)) a b
           -> Functor (cat ((C ₀) a)) (cat ((C ₀) b))
        C1 p = unFunctor' (fst ((C ₁) p))
        
        goalGrpd = (C ₀ $ (a1' , a2') , r')
        
        h1p1 = (h ₁') p₁

        z : GMorph (gcross A A ,, IdTy) ((a1' , a1') , (refl-ctor ₀' $ a1')) ((a1' , a2') , r')
        z = ((gid A a1') , r') , {!!}

        C1z : GMorph goalGrpd
                     (C1 z ₀ $ C1 ((p₁ , p₁) , _) ₀ $ h ₀' $ a1)
                     (((C1 ((gid A a1' , r') , _)) ₀) (h ₀' $ a1'))
        C1z = C1 z ₁ $ h1p1

        prf : (C1 ((p₁ , _∘_ (cat A) p₂ r) , {!!}) ₀ $ h ₀' $ a1)
            ≡ (C1 z ₀ $ C1 ((p₁ , p₁) , _) ₀ $ h ₀' $ a1)
        prf = {!!}

        goal' : GMorph goalGrpd -- (C ₀ $ (a1' , a2') , r')
                       (C1 ((p₁ , _∘_ (cat A) p₂ r) , {!!}) ₀ $ h ₀' $ a1)
                       (((C1 ((gid A a1' , r') , _)) ₀) (h ₀' $ a1'))
        goal' = substMorph {C = cat goalGrpd} (sym prf) C1z

        goal : GMorph goalGrpd -- (cat (C ₀ $ (a1' , a2') , r'))
                      (C1 ((p₁ , p₂) , q) ₀ $ C1 (((gid A a1) , r) , _) ₀ $ h ₀' $ a1)
                      (((C1 ((gid A a1' , r') , _)) ₀) (h ₀' $ a1'))
        goal = substMorph {C = cat goalGrpd} {!!} goal'
