{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Posets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Categories.Category
open import Cubical.Relation.Binary.Preorder
open import Cubical.Relation.Binary.Poset
open import Cubical.Categories.Constructions.FullSubcategory

open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint


open import Cubical.Categories.Constructions.DisplayedCategory.DisplayedPoset
open import Cubical.Categories.Constructions.DisplayedCategory.Grothendieck

private
  variable
    ℓ ℓ' : Level

open Category
open PreorderStr

-- Category of Posets
POSET : (ℓ ℓ' : Level) → Category _ _
POSET ℓ ℓ' = FullSubcategory
  (PREORDER ℓ ℓ')
  λ p → IsPoset (p .fst .snd ._≤_)


-- Trivial Display where no restrictions are placed on morphisms
PosetDisplay : DisplayedPoset (PREORDER ℓ ℓ')
PosetDisplay = record
  { D-ob = λ p → IsPoset (p .fst .snd ._≤_)
  ; D-Hom_[_,_] = λ f x y → Unit* {_}
  ; isPropHomf = isPropUnit*
  ; D-id = tt*
  ; _D-⋆_ = λ _ _ → tt*
  }

-- Same category, defined as a DisplayedPoset
POSET' : (ℓ ℓ' : Level) → Category _ _
POSET' ℓ ℓ' = Grothendieck
  (PREORDER ℓ ℓ')
  (DisplayedPoset→Cat (PREORDER ℓ ℓ') PosetDisplay)


-- Displayed Poset for picking out Posets
-- and monotone functions with adjoints
BothAdjDisplay : DisplayedPoset (PREORDER ℓ ℓ')
BothAdjDisplay = record
  { D-ob = λ p → IsPoset (p .fst .snd ._≤_)
  ; D-Hom_[_,_] = λ f x y → HasBothAdj f
  ; isPropHomf = λ {_} {_} {_} {x} → (isPropHasBothAdj x _)
  ; D-id = IdHasBothAdj
  ; _D-⋆_ = CompHasBothAdj
  }

-- Category of Posets w/ Both Adjoints
POSETADJ : (ℓ ℓ' : Level) → Category _ _
POSETADJ ℓ ℓ' = Grothendieck
  (PREORDER ℓ ℓ')
  (DisplayedPoset→Cat (PREORDER ℓ ℓ') BothAdjDisplay)

-- Displayed Poset for picking out Posets
-- and monotone functions with left adjoints
LeftAdjDisplay : DisplayedPoset (PREORDER ℓ ℓ')
LeftAdjDisplay = record
  { D-ob = λ p → IsPoset (p .fst .snd ._≤_)
  ; D-Hom_[_,_] = λ f x y → HasLeftAdj f
  ; isPropHomf = λ {_} {_} {_} {x} → (isPropHasLeftAdj x _)
  ; D-id = IdHasLeftAdj
  ; _D-⋆_ = CompHasLeftAdj
  }

POSETADJL : (ℓ ℓ' : Level) → Category _ _
POSETADJL ℓ ℓ' = Grothendieck
  (PREORDER ℓ ℓ')
  (DisplayedPoset→Cat (PREORDER ℓ ℓ') LeftAdjDisplay)

-- Displayed Poset for picking out Posets
-- and monotone functions with right adjoints
RightAdjDisplay : DisplayedPoset (PREORDER ℓ ℓ')
RightAdjDisplay = record
  { D-ob = λ p → IsPoset (p .fst .snd ._≤_)
  ; D-Hom_[_,_] = λ f x y → HasRightAdj f
  ; isPropHomf = λ {_} {_} {_} {x} → (isPropHasRightAdj x _)
  ; D-id = IdHasRightAdj
  ; _D-⋆_ = CompHasRightAdj
  }

POSETADJR : (ℓ ℓ' : Level) → Category _ _
POSETADJR ℓ ℓ' = Grothendieck
  (PREORDER ℓ ℓ')
  (DisplayedPoset→Cat (PREORDER ℓ ℓ') RightAdjDisplay)

-- TODO Rename and put somewhere else.
-- Also these might exist somewhere else
Poset→Preorder : {ℓ ℓ' : Level} → Poset ℓ ℓ'  → Preorder ℓ ℓ'
Poset→Preorder P .fst = P .fst
Poset→Preorder P .snd .PreorderStr._≤_ = P .snd .PosetStr._≤_
Poset→Preorder P .snd .PreorderStr.isPreorder .IsPreorder.is-prop-valued =
  P .snd .PosetStr.isPoset .IsPoset.is-prop-valued
Poset→Preorder P .snd .PreorderStr.isPreorder .IsPreorder.is-refl =
  P .snd .PosetStr.isPoset .IsPoset.is-refl
Poset→Preorder P .snd .PreorderStr.isPreorder .IsPreorder.is-trans =
  P .snd .PosetStr.isPoset .IsPoset.is-trans

Poset→POSETOb : {ℓ ℓ' : Level} → Poset ℓ ℓ'  → POSET ℓ ℓ' .ob
Poset→POSETOb P .fst =
  Poset→Preorder P , P .snd .PosetStr.isPoset .IsPoset.is-set
Poset→POSETOb P .snd = P .snd .PosetStr.isPoset
