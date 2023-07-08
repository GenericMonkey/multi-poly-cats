{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Subobject where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Constructions.Slice

open import Cubical.Categories.Constructions.Slice.Functor
open import Cubical.Categories.Limits.Pullback.More


module _ {ℓC ℓC' : Level} (C : Category ℓC ℓC')  where

  open Category

  private
    monic : {X : C .ob} → SliceOb C X → Type _
    monic A→X = isMonic C (A→X .S-arr)

  Mono : (C .ob) → Category _ _
  Mono X = FullSubcategory (SliceCat C X) monic



  MonoFunc : {X Y : C .ob} → (f : C [ X , Y ])
    → (pbf : PbWithf C f)
    → Functor (Mono Y) (Mono X)
  MonoFunc {X} {Y} f pbf =
    MapFullSubcategory _ monic _ monic
      (SliceFunctor C f pbf)
        λ A→Y A→Ymon →
          PBPreservesMonicL C (pbf A→Y) A→Ymon
