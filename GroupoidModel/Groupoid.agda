{-# OPTIONS --allow-unsolved-metas #-}

module GroupoidModel.Groupoid where

open import Function using (const ; _$_)
open import Utils
open import Cubical.Core.Prelude
open import CategoryTheory
open import Agda.Primitive using (lsuc ; _⊔_)

module _ {l} where

  isGroupoid : (C : Category {l} {l}) → Set _
  isGroupoid C = ∀{a b} → (f : Morph a b) → isIso C f
    where open Category C

  record Groupoid : Set (lsuc l) where
    -- no-eta-equality
    field
      cat : Category {l} {l}
      strct : isStrictCategory cat
      grpd : isGroupoid cat

  open Groupoid  

  module _ where
    open Category
    GObj : Groupoid -> Set l
    GObj G = Obj (cat G)

    GMorph : (G : Groupoid) -> GObj G -> GObj G -> Set l
    GMorph G x y = Morph (cat G) x y

    gid : (G : Groupoid) (x : GObj G) -> GMorph G x x
    gid G x = id (cat G) x

  sym-gid : (G : Groupoid) (x : GObj G) -> fst (grpd G (gid G x)) ≡ gid G x
  sym-gid G x =
    inverseUnique (cat G) (gid G x) (fst gr) (gid G x)
      (snd gr) (id∘ (id x) , id∘ (id x))
    where open Category (cat G)
          gr = (grpd G (gid G x))

module _ {l} (G : Groupoid {l}) where

  open Groupoid

  liftedIsGroupoid : isGroupoid (Lift (cat G))
  liftedIsGroupoid (MkWrap f) =
    MkWrap (fst (grpd G f)) ,
           Wrap-≡ (fst (snd (grpd G f))) ,
           Wrap-≡ (snd (snd (grpd G f)))

  LiftGrpd : Groupoid {lsuc l}
  LiftGrpd = record { cat = Lift (cat G)
                    ; strct = liftStrict (cat G) (strct G)
                    ; grpd = liftedIsGroupoid }

module _ {l} (A : Set l) (aset : isSet A) where

  -- discrete groupoid
  Δgrpd : Groupoid {l}
  Δgrpd = record { cat = Δ A aset ; strct = aset _ _
                 ; grpd = λ f → sym f , aset _ _ _ _ , aset _ _ _ _ }

module _ {l} (G H : Groupoid {l}) where

  open Groupoid

  gcross : Groupoid {l}
  cat gcross = cross (cat G) (cat H)
  strct gcross {a} {b} =
    level2-is-set (Σ-level 2
      (set-is-level2 (λ x y → strct G {x} {y})) λ _ →
       set-is-level2 λ x y → strct H {x} {y}) a b
  grpd gcross (f , g) = (fst (grpd G f) , fst (grpd H g)) ,
    ×-≡ (fst (snd (grpd G f))) (fst (snd (grpd H g))) ,
    ×-≡ (snd (snd (grpd G f))) (snd (snd (grpd H g)))

module _ {l1 l2} where

  open Groupoid

  GrpdFunctor : (G : Groupoid {l1}) (H : Groupoid {l2}) → Set _
  GrpdFunctor G H = cat G ⟶ cat H

module _ {l} where

  open Groupoid
  open Functor
  open Category

  Grpd : Category
  Grpd = record
           { Obj = Groupoid {l}
           ; Morph = GrpdFunctor
           ; id = λ G → IdFunctor (cat G)
           ; _∘_ = λ F G → compFun G F
           ; id∘ = λ {I} {J} F → Functor-≡ (FunctorEq-refl F)
           ; ∘id = λ {I} {J} F → Functor-≡ (FunctorEq-refl F)
           ; ∘∘ = λ {I} {J} {K} {L} F G H → Functor-≡ (FunctorEq-refl (compFun H (compFun G F)))
           ; hom-set = λ {G} {H} → functIsSet (cat G) (cat H) (strct G)
           }

module _ {l} where

  open Functor
  open Wrap

  gliftFunctor : Functor (Grpd {l}) (Grpd {lsuc l})
  (gliftFunctor ₀) G = LiftGrpd G
  (gliftFunctor ₁) {G} {H} F =
    MkFunct (λ x → MkWrap ((F ₀) (unWrap x)))
            (λ f → MkWrap ((F ₁) (unWrap f)))
            (λ x → Wrap-≡ (fid F (unWrap x)))
            (λ f g → Wrap-≡ (f∘ F (unWrap f) (unWrap g)))
  fid gliftFunctor G =
    Functor-≡ (record { eq0 = λ x → refl
                      ; eq1 = λ f → transpRefl _ _ · transpRefl _ _ })
  f∘  gliftFunctor = {!!}

module _ {l} {l'} {C : Category {l} {l'}} {a b c : Category.Obj C} where
  open Category

  -- record MorphOver (C : Category {l} {l'}) (a b c : Obj C) : Set (l ⊔ l') where
  --   field
  --     pp : a ≡ b
  --     mm : Morph C a c
  --   getmm : Morph C b c
  --   getmm = subst (λ z → Morph C z _) pp mm

  substMorph : -- {C : Category {l} {l'}} {a b c : Category.Obj C}
              a ≡ b -> Morph C a c -> Morph C b c
  substMorph p u = subst (λ z → Morph C z _) p u

  data PathOver (u : Morph C a c) (p : a ≡ b) (v : Morph C b c) : Set l' where
    MkPathOver : substMorph p u ≡ v -> PathOver u p v

  getPathOver : {u : Morph C a c} {p : a ≡ b} {v : Morph C b c}
              -> PathOver u p v -> substMorph p u ≡ v
  getPathOver (MkPathOver x) = x

module _ {l} {l'} {C : Category {l} {l'}} where
  open Category

  module _ {a b c d : Category.Obj C}
           {p : a ≡ b} {u : Category.Morph C a d} {v : Category.Morph C b d}
           {q : b ≡ c} {w : Category.Morph C c d}
           where

    compPathOver : PathOver {C = C} u p v -> PathOver {C = C} v q w
                 -> PathOver {C = C} u (p · q) w
    compPathOver (MkPathOver x) (MkPathOver y) = {!!}
    -- MkPathOver (subst· p q {!!} · ap (substMorph q) x · y)
   -- r (MkPathOver x) =
    -- MkPathOver {!!} -- (sym (ap (substMorph q) r) · x)

  module _ {a b c : Category.Obj C}
           {p : a ≡ b} {u : Category.Morph C a c} {v : Category.Morph C b c}
           where

    symPathOver : PathOver {C = C} u p v -> PathOver {C = C} v (sym p) u
    symPathOver (MkPathOver x) = {!!}
     -- MkPathOver (sym (ap (substMorph (sym p)) x) · subst· (sym p) p u · {!!})

  module _ {a b : Obj C} {u v : Morph C a b} where
    overRefl : u ≡ v -> PathOver {C = C} u refl v
    overRefl p = MkPathOver (transpRefl _ _ · p)

  module _ {a b c : Obj C} {u : Category.Morph C a c} {v : Category.Morph C b c} {p : a ≡ b}
           (strctCat : isStrictCategory C) where

    substPathOver : (q : a ≡ b) -> PathOver {C = C} u p v -> PathOver {C = C} u q v
    substPathOver q x = subst (λ z → PathOver u z v) {p} {q} (strctCat p q) x

  -- module _ {a b c d : Obj C} {u : Category.Morph C a d} {v : Category.Morph C c d} {p : b ≡ c} {q : a ≡ b} where

  --   collapsePathOver : PathOver {C = C} (substMorph {C = C} q u) p v -> PathOver {C = C} u (q · p) v
  --   collapsePathOver = {!!}

  module _ {a b c : Obj C} {u : Morph C a c} {q : a ≡ b} where
    collapsePathOver : PathOver {C = C} (substMorph {C = C} q u) (sym q) u
    collapsePathOver = MkPathOver {!!}

module _ {l} {l'} where
  open Groupoid
  open Functor
  open Category
  
  g-id : (G : Groupoid {l}) {x y : Obj (cat G)} (A : cat G ⟶ Grpd {l'}) (p : Morph (cat G) x y) (a : _)
      -> Morph (cat ((A ₀) y)) ((((A ₁) p) ₀) ((((A ₁) (fst (grpd G p))) ₀) a)) a
  g-id G {x} {y} A p a =
    substMorph {C = C} (sym ((apF0 _ _ _ _ a $ ap (A ₁) $ snd (snd (grpd G p))) · apF0 _ _ _ _ a (fid A y)) · apF0 _ _ _ _ a (f∘ A p p-1)) (id C a)
    where p-1 = (fst (grpd G p))
          C = cat ((A ₀) y)

