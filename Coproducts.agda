module Coproducts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.FinSet
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism
open import UMP

open Category
open Functor
open NatTrans
open UnivElt
open isUniversal

private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓj : Level

-- dual defs
⊥ᴾ : ∀ {ℓo ℓt} (C : Category ℓo ℓt) → Presheaf (C ^op) ℓ-zero
⊥ᴾ C = ⊤ᴾ (C ^op)

-- are these necessary?
push-⊥ᴾ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) → PshHom (F ^opF) (⊥ᴾ C) (⊥ᴾ D)
push-⊥ᴾ F = push-⊤ᴾ (F ^opF)

preserves-⊥ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) → Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')
preserves-⊥ {C = C}{D} F = preserves-⊤ (F ^opF)

+ᴾ : ∀ {ℓo ℓt ℓS} (C : Category ℓo ℓt) → (P Q : Presheaf (C ^op) ℓS) → Presheaf (C ^op) ℓS
+ᴾ C = ×ᴾ (C ^op)

push-+ᴾ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) (a b : C .ob)
        -- fails for silly reason : (C ^op) [-, a ] != C [ a ,-] of type
        -- → PshHom (F ^opF) (+ᴾ C (C [ a ,-]) (C [ b ,-])) (+ᴾ D (D [ F ⟅ a ⟆ ,-]) (D [ F ⟅ b ⟆ ,-]))
        → PshHom (F ^opF) (+ᴾ C ((C ^op) [-, a ]) ((C ^op) [-, b ])) (+ᴾ D ((D ^op) [-, (F ^opF)  ⟅ a ⟆ ]) ((D ^op) [-, (F ^opF) ⟅ b ⟆ ]))
push-+ᴾ F a b = push-×ᴾ (F ^opF) a b

preserves-+ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) → Type _
preserves-+ {C = C}{D} F = preserves-× (F ^opF)

Σᴾ : ∀ {ℓo ℓt ℓS} (C : Category ℓo ℓt)
              → (J : Type ℓp)
              → (J → Presheaf (C ^op) ℓS)
              → Presheaf (C ^op) (ℓ-max ℓS ℓp)
Σᴾ C = Πᴾ (C ^op)

coproduct : ∀ {ℓo ℓt ℓJ} (C : Category ℓo ℓt) (J : Type ℓJ) → (D : J → C .ob) → Type _
coproduct C J D = product (C ^op) J D

coproduct-cocone : ∀ {ℓo ℓt ℓJ} (C : Category ℓo ℓt) (J : Type ℓJ) → (D : J → C .ob) → (Σ : C .ob) → ((j : J) → C [ D j , Σ ]) → Type _
coproduct-cocone C J D Σ i = product-cone (C ^op) J D Σ i

-- open CartesianCategory

-- product-functor : {C : CartesianCategory ℓc ℓc'} (Γ : C .cat .ob) → (Functor (C .cat) (C .cat))
-- product-functor {C = C} Γ .F-ob c =  bin-prod-ob C Γ c
-- product-functor {C = C} Γ .F-hom {a} {b} f = prod₂-I C Γ b (π₁ C Γ a) (f ∘⟨ C .cat ⟩ (π₂ C Γ a))
-- product-functor {C = C} Γ .F-id {a} = {!   !} 
--   ≡⟨ {!   !} ⟩
--   prod₂-I⟨π⟩ C Γ a

-- 1 create Δ constant functor
-- prove ∀ a,b, a×b is a product
-- define -×- functor from C² → C
-- a×- = C → 1 × C → C² → C
