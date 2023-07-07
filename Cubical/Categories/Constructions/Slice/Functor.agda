{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Constructions.Slice

open Category

module Cubical.Categories.Constructions.Slice.Functor
  {ℓ ℓ' : Level} (C : Category ℓ ℓ') where

  open Functor
  open Pullback

  private
    -- helper functions
    cspn : {X Y : C .ob} (A→Y : SliceCat C Y .ob)
      → (f : C [ X , Y ])
      → Cospan C
    cspn {X} {Y} A→Y f = cospan X Y (A→Y .S-ob) f (A→Y .S-arr)

    open Cospan

    univpath : {X Y : C .ob} {A→Y B→Y : SliceCat C Y .ob}
      → (pb : Pullbacks C)
      → (f : C [ X , Y ])
      → (ϕ : (SliceCat C Y) [ A→Y , B→Y ])
      → _
    univpath {X} {Y} {A→Y} {B→Y} pb f ϕ =
      ( pb (cspn A→Y f) .pbCommutes ∙
        cong (λ x → pb (cspn A→Y f) .pbPr₂ ⋆⟨ C ⟩ x) (sym (ϕ .S-comm)) ∙
        sym (C .⋆Assoc _ _ _)
      )


    univ : {X Y : C .ob} {A→Y B→Y : SliceCat C Y .ob}
      → (pb : Pullbacks C)
      → (f : C [ X , Y ])
      → (ϕ : (SliceCat C Y) [ A→Y , B→Y ])
      → _
    univ {X} {Y} {A→Y} {B→Y} pb f ϕ =
      let pba = pb (cspn A→Y f) in
      let pbb = pb (cspn B→Y f) in
      pbb .univProp (pba .pbPr₁) (pba .pbPr₂ ⋆⟨ C ⟩ ϕ .S-hom) (univpath pb f ϕ)

  SliceFunctor : ∀ {X Y : C .ob} → (pb : Pullbacks C)
    → (f : C [ X , Y ])
    → Functor (SliceCat C Y) (SliceCat C X)
  {-
        f*A --> A
   Pr₁  |       |
        ↓       ↓
        X ----→ Y
            f
  -}
  SliceFunctor {X} {Y} pb f .F-ob A→Y =
    sliceob ( pb (cospan X Y (A→Y .S-ob) f (A→Y .S-arr)) .pbPr₁)
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
  SliceFunctor {X} {Y} pb f .F-hom {A→Y} {B→Y} ϕ =
    let pba = pb (cspn A→Y f) in
    let univb = univ pb f ϕ in
    slicehom (univb .fst .fst) (sym (univb .fst .snd .fst))
  SliceFunctor {X} {Y} pb f .F-id {A→Y} =
    let pba = pb (cspn A→Y f) in
    SliceHom-≡-intro' C X
      (pullbackArrowUnique C pba (pba .pbPr₁) (pba .pbPr₂ ⋆⟨ C ⟩ C .id)
      (univpath pb f (SliceCat C Y .id))
      {-
      (pba .pbCommutes ∙
      -- weird that this path doesn't work...
      -- cong (λ x → x ⋆⟨ C ⟩ (A→Y .S-arr)) (sym (C .⋆IdR (pba .pbPr₂)))
      cong (λ x → pba .pbPr₂ ⋆⟨ C ⟩ x) (sym ((SliceCat C Y .id) .S-comm)) ∙
      sym (C .⋆Assoc _ _ _))
      -}
      (C .id) (sym (C .⋆IdL _)) (C .⋆IdR _ ∙ sym (C .⋆IdL _)))
  SliceFunctor {X} {Y} pb f .F-seq {A→Y} {B→Y} {C→Y} ϕ ψ =
    let pba = pb (cspn A→Y f)
        pbb = pb (cspn B→Y f)
        pbc = pb (cspn C→Y f)
        univb = univ pb f ϕ
        univc = univ pb f ψ
        F⟪ϕ⟫ = SliceFunctor pb f .F-hom ϕ
        F⟪ψ⟫ = SliceFunctor pb f .F-hom ψ
    in
    SliceHom-≡-intro' C X
      (pullbackArrowUnique C pbc
        (pba .pbPr₁) ((pba .pbPr₂) ⋆⟨ C ⟩ (ϕ .S-hom ⋆⟨ C ⟩ ψ .S-hom))
        (univpath pb f (ϕ ⋆⟨ SliceCat C Y ⟩ ψ))
        {- TODO: Understand the hcomp issue here
        ( pba .pbCommutes ∙
          cong (λ x → pba .pbPr₂ ⋆⟨ C ⟩ x)
            (sym (C .⋆Assoc _ _ _ ∙
            cong (λ x → ϕ .S-hom ⋆⟨ C ⟩ x) (ψ .S-comm) ∙
            {!ϕ .S-comm!}
            )) ∙
          sym (C .⋆Assoc _ _ _)
        )
        -}
        ((F⟪ϕ⟫ .S-hom) ⋆⟨ C ⟩ (F⟪ψ⟫ .S-hom))
        ( sym (F⟪ϕ⟫ .S-comm) ∙
          cong (λ x → F⟪ϕ⟫ .S-hom ⋆⟨ C ⟩ x) (sym (F⟪ψ⟫ .S-comm)) ∙
          sym (C .⋆Assoc _ _ _)
        )
        ( sym(C .⋆Assoc _ _ _) ∙
          cong (λ x → x ⋆⟨ C ⟩ (ψ .S-hom)) (univb .fst .snd .snd) ∙
          C .⋆Assoc _ _ _ ∙
          cong (λ x → F⟪ϕ⟫ .S-hom ⋆⟨ C ⟩ x) (univc .fst .snd .snd) ∙
          sym (C .⋆Assoc _ _ _)
        )
    )
