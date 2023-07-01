{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Pullback.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors

open import Cubical.Categories.Adjoint.UniversalElements


open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Constructions.Free.Category
   renaming (rec to recCat)
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  data obs : Type₀ where
    x : obs
    y : obs
    z : obs


  data homs_quiv : Type (ℓ-suc ℓ-zero) where
    f : homs_quiv
    g : homs_quiv

  quiv : Quiver ℓ-zero (ℓ-suc ℓ-zero)
  quiv .Quiver.ob = obs
  quiv .Quiver.mor = homs_quiv
  quiv .Quiver.dom f = x
  quiv .Quiver.dom g = z
  quiv .Quiver.cod f = y
  quiv .Quiver.cod g = y

  IndexCat : Category ℓ-zero (ℓ-suc ℓ-zero)
  IndexCat = FreeCat quiv

  Cᴶ : Category _ _
  Cᴶ = FUNCTOR IndexCat C

  open Functor
  open Category
  open Cospan

  ΔPullback : Functor C Cᴶ
  ΔPullback = curryF IndexCat C {Γ = C} .F-ob (Fst C IndexCat)


  IndexCatinC : (Cospan C) → Interp quiv C
  IndexCatinC cspn .Interp.I-ob x = cspn .l
  IndexCatinC cspn .Interp.I-ob y = cspn .m
  IndexCatinC cspn .Interp.I-ob z = cspn .r
  IndexCatinC cspn .Interp.I-hom f = cspn .s₁
  IndexCatinC cspn .Interp.I-hom g = cspn .s₂

  open UnivElt
  open NatTrans

  F : (cspn : Cospan C) → Cᴶ .ob
  F cspn = recCat quiv C (IndexCatinC cspn)

  {-
    IndexCat
       f       g
    x ---> y <--- z


    F : (cspn : Cospan C) → Cᴶ .ob
      sends
         s₁       s₂
      l ---> m < --- r

      to the functor that mapping
      x ↦ l
      y ↦ m
      z ↦ r
      f ↦ s₁
      g ↦ s₂

    ΔPullback : Functor C Cᴶ
      c : C .ob
      gets sent to the constant functor always returning c and identity morphisms


    Fix some (cspn : Cospan C).
    A pullback object (pbOb : C .ob) for cspn is then just
    the data of a natural transformation from (ΔPullback ⟅ pbOb ⟆) to (F cpsn)

    As seen below,

    Pullback diagram
    pbOb --- pbPr₂ ---> r
      |                 |
    pbPr₁               s₂
      |                 |
      v                 v
      l ----- s₁ -----> m

    Natural transformation η
    ΔPullback ⟅ pbOb ⟆ --- η z ----> F z = r
          |     \__                      |
         η x       \___  η y         F g = s₂
          |            \____________     |
          v                         \    v
       F x = l ----- F f = s₁ -----> F y = m

    where pbPr₁ and pbPr₂ are the projections of the pullback object
  -}

  open isUniversal
  open Pullback

  obMap : {cspn : Cospan C} → (o : obs) → (pb : Pullback C cspn)
    → C [ pb .pbOb , F cspn ⟅ o ⟆ ]
  obMap x pb = pb .pbPr₁
  -- Could have equivalently defined this one with pb
  -- .pbPr₂ ⋆⟨ C ⟩ cspn .s₂
  -- but its a pullback so theyre the same
  obMap {cspn} y pb = pb .pbPr₁ ⋆⟨ C ⟩ cspn .s₁
  obMap z pb = pb .pbPr₂

  blah : {cspn : Cospan C} {b : C .ob} → (pb : Pullback C cspn)
    → (η : NatTrans ((ΔPullback ^opF) ⟅ b ⟆) (F cspn))
    → ∃![ hk ∈ C [ b , pb .pbOb ] ] ((η .N-ob x) ≡ hk ⋆⟨ C ⟩  pb .pbPr₁) × ((η .N-ob z) ≡ hk ⋆⟨ C ⟩  pb .pbPr₂)
  blah {cspn} {b} pb η = pb .univProp {b} (η .N-ob x) (η .N-ob z) (sym (η .N-hom (↑ f)) ∙ η .N-hom (↑ g))

  PullbackToRepresentable : ∀ {cspn} → Pullback C cspn
    → RightAdjointAt _ _ (ΔPullback) (F cspn)
  PullbackToRepresentable pb .vertex = pb .pbOb
  PullbackToRepresentable pb .element .N-ob o = obMap o pb


  -- Goal of .N-hom ϕ
  -- (((ΔPullback ^opF) ⟅ pb .pbOb ⟆) .F-hom ϕ
  --        Cubical.Categories.NaturalTransformation.Base._.⋆ᴰ
  --        PullbackToRepresentable pb .element .N-ob y₁)
  --       ≡
  --       (PullbackToRepresentable pb .element .N-ob x₁
  --        Cubical.Categories.NaturalTransformation.Base._.⋆ᴰ F cpsn .F-hom ϕ)

  PullbackToRepresentable {cspn} pb .element .N-hom {a} {b} ϕ =
    let Δₐ = ((ΔPullback ^opF) ⟅ pb .pbOb ⟆) in
    let η = (λ (o : obs) → obMap o pb) in
    elimExpProp quiv
    (λ e → C .isSetHom _ _)
    -- have naturality for f and g
    (λ {
      f → C .⋆IdL _ ;
      g → C .⋆IdL _ ∙ pb .pbCommutes
    })
    -- id is natural
    (λ {a} →
      cong (λ x → x ⋆⟨ C ⟩ η a) (Δₐ .F-id {a}) ∙
      C .⋆IdL (η a) ∙
      sym (C .⋆IdR (η a)) ∙
      cong (λ x → η a ⋆⟨ C ⟩ x) (sym ((F cspn) .F-id {a}))
    )
    -- squares stack
    (λ {a} {_} {c} e1 e2 Δe1η≡ηFe1 Δe2η≡ηFe2 →
      cong (λ x → x ⋆⟨ C ⟩ (η c)) (Δₐ .F-seq e1 e2) ∙
      C .⋆Assoc _ _ _ ∙
      cong (λ x → (Δₐ ⟪ e1 ⟫) ⋆⟨ C ⟩ x) Δe2η≡ηFe2 ∙
      sym (C .⋆Assoc _ _ _) ∙
      cong (λ x → x ⋆⟨ C ⟩ (F cspn ⟪ e2 ⟫)) Δe1η≡ηFe1 ∙
      C .⋆Assoc _ _ _ ∙
      cong (λ x → (η a) ⋆⟨ C ⟩ x ) (sym (F cspn .F-seq e1 e2))
    )
    ϕ
  PullbackToRepresentable {cspn} pb .universal .coinduction η =
    blah pb η .fst .fst
  PullbackToRepresentable {cspn} pb .universal .commutes η =
    let ab = blah pb η in
    makeNatTransPath (funExt (λ {
      x → sym (ab .fst .snd .fst) ;
      y →  ((({!refl!}  ∙
        sym (C .⋆Assoc _ _ _)) ∙
        cong (λ x → x ⋆⟨ C ⟩ F cspn ⟪ ↑ f ⟫) (sym (ab .fst .snd .fst)) ) ∙
        sym (η .N-hom (↑ f))) ∙
        C .⋆IdL (η .N-ob y) ;
      z → sym (ab .fst .snd .snd)
    }))
  PullbackToRepresentable {cspn} pb .universal .is-uniq = {!!}
