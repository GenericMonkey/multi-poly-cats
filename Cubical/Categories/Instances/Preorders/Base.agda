{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Preorders.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Relation.Binary.Preorder

open import Cubical.Categories.Instances.Preorders.Monotone

private
  variable
    ℓ ℓ' : Level

open Category

-- Category of Preorders
-- Objects are Preorders with data that type is a set
PREORDER : (ℓ ℓ' : Level) → Category _ _
PREORDER ℓ ℓ' = record
  { ob = Σ[ P ∈ Preorder ℓ ℓ' ] isSet (P .fst)
  ; Hom[_,_] = λ X Y → MonFun (X .fst) (Y .fst)
  ; id = MonId
  ; _⋆_ = MonComp
  ; ⋆IdL = λ f → eqMon _ _ refl
  ; ⋆IdR = λ f → eqMon _ _ refl
  ; ⋆Assoc = λ f g h → eqMon _ _ refl
  ; isSetHom = λ {_} {Y} → MonFunIsSet (Y .snd)
  }
