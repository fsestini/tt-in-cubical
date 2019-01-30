module GroupoidModel.IdTypes {l} where

open import Cubical.Core.Prelude
open import CategoryTheory
open import GroupoidModel.Groupoid
open import GroupoidModel.Basics
open import GroupoidModel.Universe {l}
open import Agda.Primitive

open Category
open Groupoid


Ctx : Set₁
Ctx = Σ Set (λ A → A × A) 

postulate
  _,,,_ : ∀{el el'} -> (G : Groupoid {el} {el}) -> Functor (cat G) (Grpd {el'} {el'}) -> Groupoid {el ⊔ el'} {el ⊔ el'}

Ctx' : Groupoid {lsuc l}
Ctx' = Gpd ,,, MkFunct (λ A → gcross A A) {!!} {!!} {!!}

-- small family over the groupoid [A : Set, a1 : A, a2 : A]

-- Ctxt : Groupoid {l}
-- Ctxt = (Gpd ,, MkFunct (λ A → gcross A A) {!!} {!!} {!!})

-- Id : Functor {!!} GpdCat
-- Id = {!!}
