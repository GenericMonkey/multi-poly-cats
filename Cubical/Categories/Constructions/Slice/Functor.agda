{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Constructions.Slice

open Category

module Cubical.Categories.Constructions.Slice.Functor
  {ℓ ℓ' : Level} (C : Category ℓ ℓ')
  {X Y : C .ob} (f : C [ X , Y ])
  (pbWithf : (A : SliceCat C Y .ob) →
    (Pullback C (cospan X Y (A .S-ob) f (A .S-arr))))
  where

  open Functor
  open Pullback

  private
    -- helper functions
    cspn : (A→Y : SliceCat C Y .ob) → Cospan C
    cspn A→Y = cospan X Y (A→Y .S-ob) f (A→Y .S-arr)

    open Cospan

    univpath : {A→Y B→Y : SliceCat C Y .ob}
      → (ϕ : (SliceCat C Y) [ A→Y , B→Y ])
      → (pbWithf A→Y .pbPr₁) ⋆⟨ C ⟩ f ≡
          ((pbWithf A→Y .pbPr₂) ⋆⟨ C ⟩ (ϕ .S-hom)) ⋆⟨ C ⟩ (S-arr B→Y)
    univpath {A→Y} {B→Y} ϕ =
     pbWithf A→Y .pbCommutes ∙
     cong (λ x → pbWithf A→Y .pbPr₂ ⋆⟨ C ⟩ x) (sym (ϕ .S-comm))
     ∙ sym (C .⋆Assoc _ _ _)

    univ : {A→Y B→Y : SliceCat C Y .ob}
      → (ϕ : (SliceCat C Y) [ A→Y , B→Y ])
      → _
    univ {A→Y} {B→Y} ϕ =
      (pbWithf B→Y) .univProp
        (pbWithf A→Y .pbPr₁)
        (pbWithf A→Y .pbPr₂ ⋆⟨ C ⟩ ϕ .S-hom) (univpath ϕ)

  SliceFunctor : Functor (SliceCat C Y) (SliceCat C X)
  {-
        f*A --> A
   Pr₁  |       |
        ↓       ↓
        X ----→ Y
            f
  -}
  SliceFunctor .F-ob A→Y =
    sliceob ( pbWithf A→Y .pbPr₁ )
    -- sliceob ( pb (cospan X Y (A→Y .S-ob) f (A→Y .S-arr)) .pbPr₁)
  {-
       ___________________________
      |             Pr₂           |
      |             Pr₂           ↓
     f*A ~~~~~> f*B ---> B <----- A
      |   ∃!     |       |    ϕ   |
   Pr₁|     ⟲    |       |    ⟲   |
      ↓          ↓       ↓        ↓
      X ======== X ----→ Y ====== Y
                     f
  -}
  SliceFunctor .F-hom {A→Y} {B→Y} ϕ =
    slicehom (univ ϕ .fst .fst) (sym (univ ϕ .fst .snd .fst))
  SliceFunctor .F-id {A→Y} =
    let pba = pbWithf A→Y
    in
    SliceHom-≡-intro' C X
    (pullbackArrowUnique C pba
      (pba .pbPr₁)
      ((pba .pbPr₂) ⋆⟨ C ⟩ (C .id))
      (univpath (SliceCat C Y .id))
      (C .id)
      (sym (C .⋆IdL _))
      (C .⋆IdR _ ∙ sym (C .⋆IdL _)))
  SliceFunctor .F-seq {A→Y} {B→Y} {C→Y} ϕ ψ =
    let
    pba = pbWithf A→Y
    pbb = pbWithf B→Y
    pbc = pbWithf C→Y
    univb = univ ϕ
    univc = univ ψ
    F⟪ϕ⟫ = SliceFunctor .F-hom ϕ
    F⟪ψ⟫ = SliceFunctor .F-hom ψ
    in
    SliceHom-≡-intro' C X
      (pullbackArrowUnique C pbc
        (pba .pbPr₁)
        (pba .pbPr₂ ⋆⟨ C ⟩ (ϕ .S-hom ⋆⟨ C ⟩ ψ .S-hom))
        (univpath (ϕ ⋆⟨ SliceCat C Y ⟩ ψ))
    --     {- TODO: Understand the hcomp issue here
    --     ( pba .pbCommutes ∙
    --       cong (λ x → pba .pbPr₂ ⋆⟨ C ⟩ x)
    --         (sym (C .⋆Assoc _ _ _ ∙
    --         cong (λ x → ϕ .S-hom ⋆⟨ C ⟩ x) (ψ .S-comm) ∙
    --         {!ϕ .S-comm!}
    --         )) ∙
    --       sym (C .⋆Assoc _ _ _)
    --     )
    --     -}
        (F⟪ϕ⟫ .S-hom ⋆⟨ C ⟩ F⟪ψ⟫ .S-hom)
        (sym (F⟪ϕ⟫ .S-comm) ∙
         cong (λ x → F⟪ϕ⟫ .S-hom ⋆⟨ C ⟩ x) (sym (F⟪ψ⟫ .S-comm)) ∙
         sym (C .⋆Assoc _ _ _)
        )
        (
          sym (C .⋆Assoc _ _ _) ∙
          cong (λ x → x ⋆⟨ C ⟩ ψ .S-hom) (univb .fst .snd .snd) ∙
          C .⋆Assoc _ _ _ ∙
          cong (λ x → F⟪ϕ⟫ .S-hom ⋆⟨ C ⟩ x) (univc .fst .snd .snd) ∙
          sym (C .⋆Assoc _ _ _)
        ))
