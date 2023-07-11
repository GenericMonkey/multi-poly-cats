{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Subobject where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Constructions.PosetalReflection.Base
open import Cubical.Categories.Constructions.PosetalReflection.FunctorExtension

open import Cubical.Categories.Constructions.Slice.Functor
open import Cubical.Categories.Limits.Pullback.More

open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Poset
open import Cubical.Categories.Instances.Preorders.Base

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Poset
open import Cubical.Relation.Binary.Preorder



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

  SubObject : (C .ob) → Poset _ _
  SubObject X = PosetalReflection' (Mono X)

  SubObject' : (C .ob) → Category _ _
  SubObject' X = PosetCategory (PosetalReflection' (Mono X))

  -- Feel like we may want this in the category of posets
  -- rather than just a poset
  SubObjectInPOSET : (C .ob) → POSET _ _ .ob
  SubObjectInPOSET X = PosetalReflection (Mono X)

  inducedMap : {X Y : C .ob} → (f : C [ X , Y ]) → (pbf : PbWithf C f) →
               Functor (SubObject' X) (SubObject' Y)
  inducedMap {X}{Y} f pbf = {!ReflectedFunctor (SubObject' X) (SubObject' Y) ?!}
