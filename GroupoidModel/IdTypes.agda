{-# OPTIONS --allow-unsolved-metas #-}

module GroupoidModel.IdTypes where

open import Cubical.Core.Prelude
open import CategoryTheory
open import GroupoidModel.Groupoid
open import GroupoidModel.Basics
open import Agda.Primitive
open import Function using (_$_)
open import Utils

module _ {l} (A : Groupoid {l}) where

  open Functor
  open Groupoid
  open Tm

  dupl : Functor (cat A) (cross (cat A) (cat A))
  (dupl ₀) x = x , x
  (dupl ₁) f = f , f
  fid dupl a = refl
  f∘ dupl f g = refl

  module _ where
    open Category (cat A)

    Id : Functor (cat (gcross A A)) (Grpd {l}) -- (cat Gpd)
    (Id ₀) (a1 , a2) = Δgrpd (Morph a1 a2) hom-set
    (Id ₁) {a = a1 , a2} {b = b1 , b2} (p1 , p2) =
      MkFunct (λ q → p2 ∘ (q ∘ fst (grpd A p1)))
              (ap (λ a → p2 ∘ (a ∘ fst (grpd A p1))))
              (λ x → hom-set _ _ _ _) λ f g → hom-set _ _ _ _
    fid Id (a1 , a2) =
      Functor-≡-prop _ _ hom-set
        (funExt _ λ q → ap (λ z → id a2 ∘ (q ∘ z)) (sym-gid A a1)
                      · id∘ (q ∘ id a1) · ∘id q)
    f∘ Id (f , g) (f' , g') =
      Functor-≡-prop _ _ hom-set (funExt _ goal)
      where
        subgoal1 : ((fst (grpd A f') ∘ fst (grpd A f)) ∘ (f ∘ f')) ≡ id _
        subgoal1 = {!!}
        subgoal2 : ((f ∘ f') ∘ (fst (grpd A f') ∘ fst (grpd A f))) ≡ id _
        subgoal2 = {!!}
        goal : (q : _) -> ((g ∘ g') ∘ (q ∘ fst (grpd A (f ∘ f'))))
                       ≡ (g ∘ ((g' ∘ (q ∘ fst (grpd A f'))) ∘ fst (grpd A f)))
        goal q = begin
                   ((g ∘ g') ∘ (q ∘ fst (grpd A (f ∘ f'))))
                     ≡⟨ {!!} ⟩
                   (((g ∘ g') ∘ q) ∘ fst (grpd A (f ∘ f')))
                     ≡⟨ ap (((g ∘ g') ∘ q) ∘_) (inverseUnique (cat A) (f ∘ f') _ _
                            (snd (grpd A (f ∘ f'))) (subgoal1 , subgoal2)) ⟩
                   ((((g ∘ g') ∘ q) ∘ (fst (grpd A f') ∘ fst (grpd A f))))
                     ≡⟨ {!!} ⟩
                   (g ∘ ((g' ∘ (q ∘ fst (grpd A f'))) ∘ fst (grpd A f)))
                     ∎

    refl-ctor : Tm A (compFun dupl Id)
    (refl-ctor ₀') a = gid A a
    (refl-ctor ₁') p = ap (p ∘_) (id∘ _) · snd (snd (grpd A p))
    fid' refl-ctor γ = {!!} -- hom-set _ _ _ _
    f∘' refl-ctor _ _ = {!!} -- hom-set _ _ _ _

    refl-fun : Functor (cat A) (cat (gcross A A ,, Id))
    (refl-fun ₀) x = (x , x) , (refl-ctor ₀' $ x)
    (refl-fun ₁) f = (f , f) , (refl-ctor ₁' $ f)
    fid refl-fun x = Σ-≡ (refl , hom-set _ _ _ _)
    f∘ refl-fun f g = Σ-≡ (refl , hom-set _ _ _ _)

  module _ (C : Functor (cat (gcross A A ,, Id)) (Grpd {l}))
           (h : Tm A (compFun refl-fun C)) where

    J-elim : Tm (gcross A A ,, Id) C
    (J-elim ₀') ((a1 , a2) , r) = (((C ₁) (((gid A a1) , r) , aux)) ₀) (h ₀' $ a1)
      where
        open Category (cat A)
        aux : (r ∘ (id a1 ∘ fst (grpd A (id a1)))) ≡ r
        aux = ap (r ∘_) (snd (snd (grpd A (id a1)))) · ∘id r
    (J-elim ₁') {(a1 , a2) , r} {(a1' , a2') , r'} ((p₁ , p₂) , q) = goal
      where
        p₁⁻¹ = fst (grpd A p₁)
        _∘×_ = Category._∘_ (cat (gcross A A ,, Id))
        
        C1 : ∀{a b} -> Category.Morph (cat (gcross A A ,, Id)) a b
           -> Functor (cat ((C ₀) a)) (cat ((C ₀) b))
        C1 p = (C ₁) p -- unFunctor' (fst ((C ₁) p))
        
        goalGrpd = (C ₀ $ (a1' , a2') , r')
        
        h1p1 = (h ₁') p₁

        open Category (cat A)

        z : GMorph (gcross A A ,, Id) ((a1' , a1') , (refl-ctor ₀' $ a1')) ((a1' , a2') , r')
        z = (gid A a1' , r') , ap (_∘_ r') (snd $ snd (grpd A (gid A a1'))) · ∘id r'
          
        C1z : GMorph goalGrpd
                     (C1 z ₀ $ C1 ((p₁ , p₁) , _) ₀ $ h ₀' $ a1)
                     (((C1 ((gid A a1' , r') , _)) ₀) (h ₀' $ a1'))
        C1z = C1 z ₁ $ h1p1

        aux : (p₂ ∘ r) ∘ (id a1 ∘ fst (grpd A p₁)) ≡ r'
        aux = (ap (_∘_ (p₂ ∘ r)) (id∘ _)
                · ∘∘ p₂ r _ · q · (sym $ ∘id r')
                · ap (_∘_ r') (sym $ snd $ snd (grpd A (gid A a1'))))
                · ap (_∘_ r') (snd $ snd (grpd A (gid A a1')))
                · ∘id r'

        prf : (C1 ((p₁ , p₂ ∘ r) , aux) ₀ $ h ₀' $ a1)
            ≡ (C1 z ₀ $ C1 ((p₁ , p₁) , _) ₀ $ h ₀' $ a1)
        prf = ap (λ w → (C1 w) ₀ $ (h ₀') a1) eq · (ap (_$ (h ₀' $ a1)) $ ap _₀ (f∘ C z ((p₁ , p₁) , _)))
          where
            q' : p₂ ∘ r ≡ r' ∘ p₁
            q' = ap (p₂ ∘_) (sym (∘∘ r p₁⁻¹ p₁ · (ap (r ∘_) (fst (snd (grpd A p₁)))
                 · ∘id r))) · sym (∘∘ p₂ (r ∘ p₁⁻¹) p₁) · ap (_∘ p₁) q
            eq : ((p₁ , p₂ ∘ r) , aux)
               ≡ (_∘×_ z ((p₁ , p₁) , (refl-ctor ₁') p₁))
            eq = Σ-prop-≡ (λ x → hom-set _ _) (×-≡ (sym (id∘ p₁)) q')

        goal' : GMorph goalGrpd
                       (C1 ((p₁ , p₂ ∘ r) , _) ₀ $ h ₀' $ a1)
                       (((C1 ((gid A a1' , r') , _)) ₀) (h ₀' $ a1'))
        goal' = substMorph {C = cat goalGrpd} (sym prf) C1z

        prf2 : ((C1 ((p₁ , p₂ ∘ r) , aux) ₀) $ (h ₀') $ a1)
             ≡ ((C1 ((p₁ , p₂) , q) ₀) $ (C1 ((gid A a1 , r) , _) ₀) $ (h ₀') $ a1)
        prf2 = {!!} · (ap (_$ (h ₀' $ a1)) $ ap _₀ (f∘ C ((p₁ , p₂) , q) ((gid A a1 , r) , _)))

        goal : GMorph goalGrpd
                      (C1 ((p₁ , p₂) , q) ₀ $ C1 (((gid A a1) , r) , _) ₀ $ h ₀' $ a1)
                      (((C1 ((gid A a1' , r') , _)) ₀) (h ₀' $ a1'))
        goal = substMorph {C = cat goalGrpd} prf2 goal'
    fid' J-elim _ = {!!}
    f∘' J-elim = {!!}

module _ {l} (Γ : Groupoid {l}) (A : Ty Γ) where

  open Groupoid

  IdType : Ty ((Γ ,, A) ,, compFun (π₁ (Γ ,, A) (IdFunctor (cat (Γ ,, A)))) A)
  IdType = compFun (rearrange Γ A) (Id (Γ ,, A))
