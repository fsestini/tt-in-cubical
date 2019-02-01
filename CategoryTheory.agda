{-# OPTIONS --allow-unsolved-metas #-}

module CategoryTheory where

open import Cubical.Core.Glue
open import Cubical.Basics.Equiv
open import Utils
open import Function using (_$_ ; const)
open import Agda.Primitive
open import Cubical.Core.Prelude hiding (_∧_ ; _×_)
-- open import IrrelevantProp
open import Data.Product

record Category {l} {l'} : Set (lsuc (l ⊔ l')) where
  no-eta-equality
  field
    Obj : Set l
    Morph : Obj → Obj → Set l'
    id    : ∀ I → Morph I I
    _∘_   : ∀{I J K : Obj} → Morph J K → Morph I J → Morph I K

    hom-set : ∀{a b : Obj} → isSet (Morph a b)
    id∘   : ∀{i j} (f : Morph i j) → id j ∘ f ≡ f
    ∘id   : ∀{i j} (f : Morph i j) → f ∘ id i ≡ f
    ∘∘    : ∀{i j k l} (f : Morph k l) (g : Morph j k) (h : Morph i j)
          → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

module _ {l} (A : Set l) (aset : isSet A) where

  open Category

  -- discrete category
  Δ : Category {l} {l}
  Obj Δ = A
  Morph Δ a b = a ≡ b
  id Δ x = refl
  _∘_ Δ p q = q · p
  hom-set Δ = propIsSet _ (aset _ _)
  id∘ Δ f = aset _ _ _ f
  ∘id Δ f = aset _ _ _ _
  ∘∘ Δ _ _ _ = aset _ _ _ _

module _ {l} {l'} {l''} {l'''} (C : Category {l} {l'}) (D : Category {l''} {l'''}) where

  open Category

  cross : Category
  Obj cross = Obj C × Obj D
  Morph cross (c , d) (c' , d') = Morph C c c' × Morph D d d'
  id cross (x , y) = (id C x) , (id D y)
  _∘_ cross (f , f') (g , g') = _∘_ C f g , _∘_ D f' g'
  hom-set cross = {!!}
  id∘ cross f = {!!}
  ∘id cross f = {!!}
  ∘∘ cross f g = {!!}

module _ {l} {l'} (C : Category {l} {l'}) where

  open Category C

  isIso : ∀{a b} → Morph a b → Set _
  isIso {a} {b} f = Σ (Morph b a) λ g → g ∘ f ≡ id _ × f ∘ g ≡ id _

  isIsoIsProp : ∀{a b} -> (u : Morph a b) -> isProp (isIso u)
  isIsoIsProp u = {!!}

  _≅_ : Obj -> Obj -> Set _
  A ≅ B = Σ (Morph A B) isIso

  module _ {A B : Obj} where

    ≅IsSet : isSet (A ≅ B)
    ≅IsSet = Σ-subset hom-set isIsoIsProp

    idtoiso : A ≡ B -> A ≅ B
    idtoiso = J (λ B' p → A ≅ B') (id A , id A , id∘ _ , id∘ _)

    -- idtoiso-equiv : isEquiv idtoiso -> isSet (A ≡ B)
    -- idtoiso-equiv eqv = subst isSet (ua ({!!} , {!!})) ≅IsSet

  isPreCategory : Set _
  isPreCategory = ∀{a b : Obj} → {f g : Morph a b} → isProp (f ≡ g)

  isStrictCategory : Set _
  isStrictCategory = ∀{a b : Obj} → isProp (a ≡ a)

  _ᵒᵖ : Category
  _ᵒᵖ = record
          { Obj = Obj
          ; Morph = λ x y → Morph y x
          ; _∘_ = λ f g → g ∘ f
          ; id = id
          ; ∘∘ = λ { f g h → let aux = ∘∘ h g f in sym aux }
          ; id∘ = λ { f → ∘id f }
          ; ∘id = λ { f → id∘ f }
          ; hom-set = hom-set
          }

module _ {l l' l'' l'''} (C : Category {l} {l'}) (D : Category {l''} {l'''}) where

  record Functor : Set (l ⊔ l' ⊔ l'' ⊔ l''') where
    constructor MkFunct
    open Category
    field
      _₀ : Obj C → Obj D
      _₁ : ∀{a b} → Morph C a b → Morph D (_₀ a) (_₀ b)
      fid : (∀ x → _₁ (id C x) ≡ id D (_₀ x))
      f∘  : (∀{i j k} (f : Morph C j k) (g : Morph C i j)
          → _₁ (_∘_ C f g) ≡ _∘_ D (_₁ f) (_₁ g))

  record Functor' : Set (lsuc (l ⊔ l' ⊔ l'' ⊔ l''')) where
    constructor MkFunctor'
    field
      unFunctor' : Functor

  -- record Functor' : Set (lsuc (l ⊔ l' ⊔ l'' ⊔ l''')) where
  --   constructor MkFunct'
  --   open Category
  --   field
  --     _₀ : Obj C → Obj D
  --     _₁ : ∀{a b} → Morph C a b → Morph D (_₀ a) (_₀ b)
  --     fid : (∀ x → _₁ (id C x) ≡ id D (_₀ x))
  --     f∘  : (∀{i j k} (f : Morph C j k) (g : Morph C i j)
  --         → _₁ (_∘_ C f g) ≡ _∘_ D (_₁ f) (_₁ g))

  -- fun' : Functor' -> Functor
  -- fun' (MkFunct' _₀ _₁ fid f∘) = MkFunct _₀ _₁ fid f∘

  _⟶_ = Functor

  module _ where
    open Category

    ObjPart : Set _
    ObjPart = Obj C → Obj D

    MorphPart : ObjPart → Set _
    MorphPart _₀ = ∀{a b} → Morph C a b → Morph D (_₀ a) (_₀ b)

    Functoriality : (o : ObjPart) -> MorphPart o -> Set _
    Functoriality F₀ F₁ =
        (∀ x → F₁ (id C x) ≡ id D (F₀ x))
      × (∀{i j k} (f : Morph C j k) (g : Morph C i j)
           → F₁ (_∘_ C f g) ≡ _∘_ D (F₁ f) (F₁ g))

    functIsProp : (o : ObjPart) -> (m : MorphPart o) -> isProp (Functoriality o m)
    functIsProp F₀ F₁ = ×-prop (Π-prop (λ x → hom-set D _ _))
      λ f g → funExt' _ $ λ i → funExt' _ $ λ j → funExt' _ $ λ k → funExt _ $ λ x →
        funExt _ (λ y → hom-set D _ _ (f x y) (g x y))

    funct≃Σ : Functor ≃ Σ (Σ ObjPart MorphPart) λ { (o , m) → Functoriality o m }
    funct≃Σ =
      isoToEquiv
        (λ { (MkFunct F₀ F₁ x y) → (F₀ , F₁) , (x , y) })
        (λ { ((F₀ , F₁) , (x , y)) → MkFunct F₀ F₁ x y })
        (λ { ((F₀ , F₁) , (x , y)) → refl })
        (λ { (MkFunct _₀ _₁ fid₁ f∘₁) → refl })

    Functor-≡ : (F G : Functor) -> fst (fst funct≃Σ F) ≡ fst (fst funct≃Σ G) -> F ≡ G
    Functor-≡ F G h = ≡-on-≃ funct≃Σ (Σ-prop-≡ (λ { (x , y) → functIsProp x y}) h)

    functIsSet : isStrictCategory C -> isSet Functor
    functIsSet k =
      subst isSet (sym (ua funct≃Σ))
        (Σ-subset (Σ-set {!!} {!!}) (λ { (o , m) → functIsProp {!!} {!!} }))

    module _ (F G : Functor) where
      open Functor

      apF0 : (x : _) -> F ≡ G -> (F ₀) x ≡ (G ₀) x
      apF0 x p = ap (_$ x) (ap _₀ p)

      RawNatTrans : Set _
      RawNatTrans = (c : Obj C) → Morph D ((F ₀) c) ((G ₀) c)

      isNatural : RawNatTrans → Set _
      isNatural ϕ = ∀{C₁ C₂} (f : Morph C C₁ C₂)
                  → _∘_ D ((G ₁) f) (ϕ C₁) ≡ _∘_ D (ϕ C₂) ((F ₁) f)

      natrltyIsProp : (ϕ : RawNatTrans) -> isProp (isNatural ϕ)
      natrltyIsProp ϕ h h' =
        funExt' _ $ λ _ → funExt' _ λ _ → funExt _ $ λ x → hom-set D _ _ (h x) (h' x)

      NatTrans : Set _
      NatTrans = Σ RawNatTrans isNatural

      ≡-nt : (ϕ ψ : NatTrans) -> fst ϕ ≡ fst ψ -> ϕ ≡ ψ
      ≡-nt ϕ ψ p = Σ-prop-≡ natrltyIsProp p

  IdNatTrans : {F : Functor} → NatTrans F F
  IdNatTrans {F} = (λ c → id ((F ₀) c)) , λ f →
      ∘id ((F ₁) f) · sym (id∘ ((F ₁) f))
    where open Functor ; open Category D

  [_,_] : Category
  [_,_] = record
            { Obj = Functor
            ; Morph = λ F G → NatTrans F G
            ; _∘_ = λ {I} {J} {K} ϕ ψ → (λ c → fst ϕ c ∘ fst ψ c) ,
               λ {C₁} f → sym (∘∘ ((K ₁) f) (fst ϕ _) (fst ψ _))
                          · cong (_∘ fst ψ C₁) (snd ϕ _)
                          · ∘∘ (fst ϕ _) ((J ₁) f) (fst ψ _)
                          · cong (fst ϕ _ ∘_) (snd ψ _)
                          · sym (∘∘ _ _ _)
            ; id = λ F → IdNatTrans {F}
            ; ∘∘ = λ {I} {_} {_} {L} f g h →
                ≡-nt I L _ _ (funExt _ λ x → ∘∘ (fst f x) (fst g x) (fst h x))
            ; id∘ = λ {I} {J} f → ≡-nt I J _ _ (funExt _ (λ x → id∘ (fst f x)))
            ; ∘id = λ {I} {J} f → ≡-nt I J _ _ (funExt _ (λ x → ∘id (fst f x)))
            ; hom-set = λ {F} {G} → Σ-subset (Π-set λ x → hom-set) (natrltyIsProp F G)
            }
    where open Category D ; open Functor

module _ {la la' lb lb' lc lc' ld ld'}
  {A : Category {la} {la'}}
  {B : Category {lb} {lb'}}
  {C : Category {lc} {lc'}}
  {D : Category {ld} {ld'}}
  (F : Functor A B) (G : Functor C D)
  where

  open Category
  open Functor

  cross-fun : Functor (cross A C) (cross B D)
  _₀ cross-fun (a , c) = (F ₀ $ a) , (G ₀ $ c)
  _₁ cross-fun (f , g) = (F ₁ $ f) , (G ₁ $ g)
  fid cross-fun (x , y) = cong2 _,_ (fid F x) (fid G y)
  f∘ cross-fun (f1 , f2) (g1 , g2) = cong2 _,_ (f∘ F f1 g1) (f∘ G f2 g2)

Sets : ∀{l} → Category
Sets {l} = record
           { Obj = Σ (Set l) isSet -- Set l
           ; Morph = λ A B → fst A → fst B
           ; _∘_ = λ z z₁ z₂ → z (z₁ z₂)
           ; id = λ _ x → x
           ; ∘∘ = λ _ _ _ → refl
           ; id∘ = λ _ → refl
           ; ∘id = λ _ → refl
           ; hom-set = λ {a} {b} → →-set (snd a) (snd b)
           }

module _ {l} {l'} (C : Category {l} {l'}) where

  IdFunctor : Functor C C
  IdFunctor = MkFunct (λ x → x) (λ x → x) (λ _ → refl) (λ _ _ → refl)

  open Category

  ConstFunctor : ∀{dl dl'} (D : Category {dl} {dl'}) (c : Obj C)
               -> Functor D C
  ConstFunctor D c =
    MkFunct (λ _ → c) (λ _ → id C c) (λ _ → refl) λ _ _ → sym $ id∘ C _               

module _ {lc} {lc'} {ld} {ld'} {le} {le'}
  (C : Category {lc} {lc'})
  (D : Category {ld} {ld'})
  (E : Category {le} {le'}) where

  open Functor
  open Category

  compFun : (F : Functor C D) (G : Functor D E) → Functor C E
  _₀ (compFun F G) x = (G ₀) ((F ₀) x)
  _₁ (compFun F G) f = (G ₁) ((F ₁) f)
  fid (compFun F G) x = cong (G ₁) (fid F x) · fid G ((F ₀) x)
  f∘ (compFun F G) f g = {!!}

module _ {l l' l''} (C : Category {l} {l'}) where

  open Category C
  open Functor

  PSh : Set _
  PSh = Functor (C ᵒᵖ) (Sets {l''})

  PShCat : Category
  PShCat = [ C ᵒᵖ , Sets {l''} ]

  open import Function using (_$_)

  module Elements (cStrictCat : isStrictCategory C) where

    ∫ : PSh → Category
    Obj (∫ P) = Σ Obj (λ A → fst ((P ₀) A)) -- Σ Obj (P ₀)
    Morph (∫ P) (J , γ') (I , γ) = Σ (Morph J I) (λ u → (P ₁) u γ ≡ γ')
    _∘_ (∫ P) {I} {J} {K} (u , p) (u' , p') =
      (u ∘ u') , cong (_$ snd K) (f∘ P u' u) · cong ((P ₁) u') p · p'

    id (∫ P) x = id (fst x) , cong (_$ snd x) (fid P (fst x))
    ∘∘ (∫ P) f g h = Σ-prop-≡ (λ x → snd ((P ₀) (fst _)) _ _) (∘∘ (fst f) (fst g) (fst h))
    id∘ (∫ P) = λ f → Σ-prop-≡ {!!} (id∘ (fst f))
    ∘id (∫ P) = λ f → Σ-prop-≡ {!!} (∘id (fst f))
    hom-set (∫ P) {a1 , a2} {b1 , b2} = Σ-set hom-set λ u → {!!}

    uhm : {P Q : PSh}
        → Functor ((∫ Q) ᵒᵖ) (Sets {l''}) → NatTrans (C ᵒᵖ) (Sets {l''}) P Q
        → Functor ((∫ P) ᵒᵖ) (Sets {l''})
    _₀ (uhm A ϕ) (I , γ) = (A ₀) (I , fst ϕ I γ)
    _₁ (uhm A ϕ) {a = (I , γ)} (u , p) x =
      (A ₁) (u , cong (_$ γ) (snd ϕ u) · cong (fst ϕ _) p) x
    fid (uhm A ϕ) x = funExt _ (λ y → {!!}) -- fid A >>= λ f → ∣ (λ _ → f _) ∣
    f∘ (uhm A ϕ) = {!!}
      -- do
      -- fA <- f∘ A
      -- ∣ (λ {i} {j} {k} f g →
      --   fA (fst' f , cong (_$ snd j) <$> snd' ϕ (fst' f) ● cong (fst' ϕ (fst k)) <$> snd' f)
      --      (fst' g , cong (_$ snd i) <$> snd' ϕ (fst' g) ● cong (fst' ϕ (proj₁ j)) <$> snd' g)) ∣

record HasTerminalObj {l l'} (C : Category {l} {l'}) : Set (l ⊔ l') where
  open Category C
  field
    one : Obj
    bang : (x : Obj) → Morph x one
    uniq : (x : Obj) → (f : Morph x one) → f ≡ bang x
      -- (one' : Obj) → ((x : Obj) → Morph x one') → _≃_ {C = C} one one' 

module _ where
  open HasTerminalObj

  terminalSets : ∀{l} → HasTerminalObj (Sets {l})
  one terminalSets = ⊤ , ⊤-is-set
  bang terminalSets = λ _ _ → tt
  uniq terminalSets = λ x f → refl

module _ {l} {l'} {l''} (C : Category {l} {l'}) where

  open Category
  open HasTerminalObj

  PShTerm : HasTerminalObj (PShCat {l'' = l''} C)
  one PShTerm =
    record { _₀ = λ _ → one terminalSets
           ; _₁ = λ _ x → x
           ; fid = const refl
           ; f∘ = λ _ _ → refl }
  bang PShTerm _ = (λ _ _ → tt) , λ _ → refl
  uniq PShTerm _ _ = refl
