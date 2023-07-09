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
  -- Given a morphism [ϕ] from [x] to [y] (which is just an ordering [x] ≤c [y]), we want
  -- to construct a morphism from [F ⟅ x ⟆] to [F ⟅ y ⟆] (which is just an ordering [F ⟅ x ⟆] ≤d [F ⟅ y ⟆]).
  -- This should be done by deconstructing [ϕ] into some underlying morphism on representatives
  -- ϕ : x → y and then using [F ⟪ ϕ ⟫] to get a morphism from [F ⟅ x ⟆] to [F ⟅ y ⟆].
  -- The tricky part is understanding what [F ⟪ ϕ ⟫] should be
  ReflectedFunctor .F-hom {[x]}{[y]} [ϕ] =
    rec2p
    -- TODO some sort of isProp
    {!!}
    (λ (x , xrep) (y , yrep) →
      elimp
      -- TODO some sort of isProp
      ({!!})
      (λ ϕ →
        transport (cong (λ z → ⟨ [ F ⟅ x ⟆ ]ₛ ≤d ReflectedFunctor ⟅ z ⟆ ⟩) yrep ∙
                   cong (λ z → ⟨ ReflectedFunctor ⟅ z ⟆ ≤d ReflectedFunctor ⟅ [y] ⟆ ⟩) xrep)
                   -- TODO termination issue on the line above, may clear up after holes are filled
        ∣ F ⟪ ϕ ⟫ ∣₁
      )
      (transport
        (sym(cong (λ z → ⟨ [ x ]ₛ ≤c z ⟩) yrep ∙
          cong
        (λ z → ⟨ z ≤c [y] ⟩) xrep)) [ϕ])
    )
    ([]surjective [x])
    ([]surjective [y])
  -- TODO I have no idea if this F-id is remotely correct
  ReflectedFunctor .F-id {[x]} =
    elim
    {P = λ [c] → ReflectedFunctor .F-hom (isRefl≤q C [c]) ≡ isRefl≤q D (ReflectedFunctor .F-ob [c])}
    {!!}
    (λ c i → ∣ F .F-id {c} i ∣₁)
    {!!}
    [x]
  -- TODO F-seq should probably be some sort of is-trans??
  ReflectedFunctor .F-seq [f] [g] = {!!}

-- ReflectedFunctor .F-hom (isRefl≤q C [x]) ≡
      -- isRefl≤q D (ReflectedFunctor .F-ob [x])
