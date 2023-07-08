{-
  The posetal reflection of a category. That is, take the preorder obtained by
  saying that A ≤ B if there is a morphism from A to B, and then take the
  poset obtained by quotienting by the equivalence relation A ≤ B and B ≤ A.
-}
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.PosetalReflection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.Logic

open import Cubical.HITs.SetQuotients renaming ([_] to [_]ₛ)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to recp ; rec2 to rec2p)

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Poset
open import Cubical.Relation.Binary.Preorder

private
  variable
    ℓC ℓC' : Level

module _ (C : Category ℓC ℓC') where

  open Category
  open PreorderStr
  open IsPreorder
  open BinaryRelation

  PreorderReflection : Preorder ℓC ℓC'
  PreorderReflection .fst = C .ob
  PreorderReflection .snd ._≤_ c c' = ∥ C [ c , c' ] ∥₁
  PreorderReflection .snd .isPreorder .is-prop-valued c c' = isPropPropTrunc
  PreorderReflection .snd .isPreorder .is-refl c = ∣ C .id {c} ∣₁
  PreorderReflection .snd .isPreorder .is-trans c c' c'' =
    rec2p isPropPropTrunc (λ f g → ∣ f ⋆⟨ C ⟩ g ∣₁)

  _≤p_ : PreorderReflection .fst → PreorderReflection .fst → hProp _
  c ≤p c' = (PreorderReflection .snd ._≤_ c c') , isPropPropTrunc

  OrderEquiv : C .ob → C .ob → Type _
  OrderEquiv c c' = Σ ((c ≤p c') .fst)
                      (λ _ → (c' ≤p c) .fst)

  isPropValuedOrderEquiv : isPropValued OrderEquiv
  isPropValuedOrderEquiv c c' =
    λ x y →
      ΣPathP (((c ≤p c') .snd (x .fst) (y .fst)) ,
              ((c' ≤p c) .snd (x .snd) (y .snd)))

  isReflOrderEquiv : isRefl OrderEquiv
  isReflOrderEquiv c = (PreorderReflection .snd .isPreorder .is-refl c) ,
                       ((PreorderReflection .snd .isPreorder .is-refl c))

  isSymOrderEquiv : isSym OrderEquiv
  isSymOrderEquiv a b aOEb = (aOEb .snd) , (aOEb .fst)

  isTransOrderEquiv : isTrans OrderEquiv
  isTransOrderEquiv a b c aOEb bOEc =
    (PreorderReflection .snd .isPreorder .is-trans
      a b c (aOEb .fst) (bOEc .fst)) ,
    (PreorderReflection .snd .isPreorder .is-trans
      c b a (bOEc .snd) (aOEb .snd))

  isEquivRelOrderEquiv : isEquivRel OrderEquiv
  isEquivRelOrderEquiv =
    equivRel isReflOrderEquiv isSymOrderEquiv isTransOrderEquiv

  QuotientByOrderEquiv : Type _
  QuotientByOrderEquiv = C .ob / OrderEquiv

  isSetQuotientByOrderEquiv : isSet QuotientByOrderEquiv
  isSetQuotientByOrderEquiv = squash/

  _≤q_ : QuotientByOrderEquiv → QuotientByOrderEquiv → hProp _
  [c] ≤q [c'] =
    rec2 isSetHProp _≤p_
      (λ a b c x → ⇔toPath
         (λ y → PreorderReflection .snd .isPreorder .is-trans
                b a c (x .snd) y)
         (λ z → PreorderReflection .snd .isPreorder .is-trans
                a b c (x .fst) z)
      )
      (λ a b c x → ⇔toPath
        (λ y → PreorderReflection .snd .isPreorder .is-trans
               a b c y (x .fst))
        (λ z → PreorderReflection .snd .isPreorder .is-trans
               a c b z (x .snd))
      )
      [c]
      [c']

  isRefl≤q : isRefl λ a b → ⟨ _≤q_ a b ⟩
  isRefl≤q =
    elimProp
      (λ [x] → str ([x] ≤q [x]))
      (PreorderReflection .snd .isPreorder .is-refl)

  isTrans≤q : isTrans λ a b → ⟨ _≤q_ a b ⟩
  isTrans≤q =
    elimProp3
      (λ [a] [b] [c] → isProp→ (isProp→ (str ([a] ≤q [c])))  )
      ( (PreorderReflection .snd .isPreorder .is-trans) )

  isAntisym≤q : isAntisym λ a b → ⟨ _≤q_ a b ⟩
  isAntisym≤q [a] [b] [a]≤q[b] [b]≤q[a] =
    rec2p
    (isSetQuotientByOrderEquiv [a] [b])
    (λ (a , arep) (b , brep) →
      sym arep ∙
      isEquivRel→effectiveIso
        isPropValuedOrderEquiv
        isEquivRelOrderEquiv
        a
        b .Iso.inv
          (
          transport
            (sym ((cong (λ x → ⟨ [ a ]ₛ ≤q x ⟩) brep) ∙
            (cong (λ x → ⟨ x ≤q [b] ⟩) arep))) [a]≤q[b] ,
          transport
            (sym ((cong (λ x → ⟨ x ≤q [ a ]ₛ ⟩) brep) ∙
            (cong (λ x → ⟨ [b] ≤q x ⟩) arep))) [b]≤q[a]
          )
      ∙ brep
    )
    ([]surjective [a])
    ([]surjective [b])

  PosetalReflection : Poset _ _
  PosetalReflection .fst = C .ob / OrderEquiv
  PosetalReflection .snd =
    posetstr (λ a b → ⟨ a ≤q b ⟩)
    (isposet
      isSetQuotientByOrderEquiv
      (λ a b → str (a ≤q b))
      isRefl≤q
      isTrans≤q
      isAntisym≤q)
