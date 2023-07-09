{-
  The posetal reflection of a category. That is, take the preorder obtained by
  saying that A ≤ B if there is a morphism from A to B, and then take the
  poset obtained by quotienting by the equivalence relation A ≤ B and B ≤ A.
-}
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.PosetalReflection.FunctorExtension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.Logic

open import Cubical.HITs.SetQuotients renaming ([_] to [_]ₛ)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to recp ; rec2 to rec2p; elim to elimp)

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Poset
open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Poset
open import Cubical.Relation.Binary.Preorder

open import Cubical.Categories.Constructions.PosetalReflection.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ (C : Category ℓC ℓC')
         (D : Category ℓD ℓD')
         (F : Functor C D) where

  open Category
  open Functor

  _≤c_ : QuotientByOrderEquiv C → QuotientByOrderEquiv C → hProp _
  _≤c_ = _≤q_ C

  _≤d_ : QuotientByOrderEquiv D → QuotientByOrderEquiv D → hProp _
  _≤d_ = _≤q_ D

  ReflectedFunctor : Functor (PosetCategory (PosetalReflection' C))
                             (PosetCategory (PosetalReflection' D))
  ReflectedFunctor .F-ob x =
    rec
      squash/
      (λ c → [ F ⟅ c ⟆ ]ₛ)
      (λ a b aOEb → eq/ (F ⟅ a ⟆) (F ⟅ b ⟆)
        (
        elimp (λ _ → isPropPropTrunc) (λ f → ∣ F ⟪ f ⟫ ∣₁) (aOEb .fst) ,
        elimp (λ _ → isPropPropTrunc) (λ f → ∣ F ⟪ f ⟫ ∣₁) (aOEb .snd)))
      x
  -- TODO Given a morphism [ϕ] from [x] to [y] (which is just an ordering [x] ≤c [y]), we want
  -- to construct a morphism from [F ⟅ x ⟆] to [F ⟅ y ⟆] (which is just an ordering [F ⟅ x ⟆] ≤d [F ⟅ y ⟆]).
  -- This should be done by deconstructing [ϕ] into some underlying morphism on representatives
  -- ϕ : x → y and then using [F ⟪ ϕ ⟫] to get a morphism from [F ⟅ x ⟆] to [F ⟅ y ⟆].
  -- The tricky part is understanding what [F ⟪ ϕ ⟫] should be
  ReflectedFunctor .F-hom {[x]}{[y]} [ϕ] =
    rec2p
    {!should be is-prop-valued or isSetHom!}
    (λ (x , xrep) (y , yrep) →
      elimp
      (λ _ → {!should be is-prop-valued or isSetHom!})
      -- Here we turn [ϕ] into an actual morphism ϕ and should be able to do something with it
      (λ ϕ → {!F ⟪ ϕ ⟫!})
      (transport
        (sym(cong (λ z → ⟨ [ x ]ₛ ≤c z ⟩) yrep ∙
          cong
        (λ z → ⟨ z ≤c [y] ⟩) xrep)) [ϕ])
    )
    ([]surjective [x])
    ([]surjective [y])
  ReflectedFunctor .F-id = {!!}
  ReflectedFunctor .F-seq f g = {!!}
