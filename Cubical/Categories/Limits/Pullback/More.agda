{-# OPTIONS --safe #-}

-- results about pullbacks
module Cubical.Categories.Limits.Pullback.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Constructions.Free.Category
   renaming (rec to recCat)
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where

  open Cospan
  open Pullback
  open Category

  PBPreservesMonicL :
    (cspn : Cospan C) → (pb : Pullback C cspn)
    → isMonic C (cspn .s₂)
    → isMonic C (pb .pbPr₁)
  PBPreservesMonicL cspn pb s2mon {_} {a} {a'} =
    let pr₁ = pb .pbPr₁
        pr₂ = pb .pbPr₂
    in
    (λ apr₁≡a'pr₁ →
    -- a == univ-prop for apr₁ and apr₂ (easy)
    (sym (cong (fst)
      (pb .univProp (a ⋆⟨ C ⟩ pr₁) (a ⋆⟨ C ⟩ pr₂)
        (C .⋆Assoc _ _ _ ∙
        (cong (λ x → a ⋆⟨ C ⟩ x) (pb .pbCommutes)) ∙
        sym (C .⋆Assoc _ _ _))
          .snd (a , refl , refl)
      )
    )) ∙
    -- proof that a' is a univ prop for apr₁ and apr₂
    (cong (fst)
      (pb .univProp (a ⋆⟨ C ⟩ pr₁) (a ⋆⟨ C ⟩ pr₂)
        (C .⋆Assoc _ _ _ ∙
        (cong (λ x → a ⋆⟨ C ⟩ x) (pb .pbCommutes)) ∙
        sym (C .⋆Assoc _ _ _))
          .snd (a' ,
            apr₁≡a'pr₁ ,
            s2mon
              (C .⋆Assoc _ _ _ ∙
              cong (λ x → a ⋆⟨ C ⟩ x) (sym (pb .pbCommutes)) ∙
              sym (C .⋆Assoc _ _ _) ∙
              cong (λ x → x ⋆⟨ C ⟩ (cspn .s₁)) apr₁≡a'pr₁ ∙
              (C .⋆Assoc _ _ _) ∙
              cong (λ x → a' ⋆⟨ C ⟩ x) (pb .pbCommutes) ∙
              sym (C .⋆Assoc _ _ _))
          )
      )
    ))

  PBPreservesMonicR :
    (cspn : Cospan C) → (pb : Pullback C cspn)
    → isMonic C (cspn .s₁)
    → isMonic C (pb .pbPr₂)
  PBPreservesMonicR cspn pb s1mon =
    PBPreservesMonicL
      (cospan (cspn .r) (cspn .m) (cspn .l) (cspn .s₂) ( cspn .s₁))
      (record
         { pbOb = pb .pbOb
         ; pbPr₁ = pb .pbPr₂
         ; pbPr₂ = pb .pbPr₁
         ; pbCommutes = sym (pb .pbCommutes)
         ; univProp = λ h k H' →
           ( pb .univProp k h (sym H') .fst .fst ,
             pb .univProp k h (sym H') .fst .snd .snd ,
             pb .univProp k h (sym H') .fst .snd .fst
            ) , λ (a , (b1 , b2)) →
              let univ = (pb .univProp k h (sym H') .snd (a , (b2 , b1)))
                  hk≡ = cong (fst) univ
                  k≡ = cong (λ x → x .snd .fst) univ
                  h≡ = cong (λ x → x .snd .snd) univ
              in
              ΣPathP ( hk≡ , ΣPathP ( h≡ , k≡ ))
         }) s1mon

  -- Pullbacks Representability
module PBRepresentable (C : Category ℓ ℓ') where
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

  Functor→Cospan : (Cᴶ .ob) → (Cospan C)
  Functor→Cospan Fun =
    cospan
      (Fun .F-ob x)
      (Fun .F-ob y)
      (Fun .F-ob z)
      (Fun .F-hom ( ↑ f ))
      (Fun .F-hom ( ↑ g ))

  ΔPullback : Functor C Cᴶ
  ΔPullback = curryF IndexCat C {Γ = C} .F-ob (Fst C IndexCat)

  open Cospan

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

  ShiftCospanR : {b : C .ob} → (cspn : Cospan C)
    → (C [ b , cspn .m ])
    → Cospan C
  ShiftCospanR {b} cspn ϕ = cospan (cspn .l) (cspn .m) b (cspn .s₁) ϕ

  FLiftIsoR : {b : C .ob} {cspn : Cospan C}
    → (ϕ : C [ b , cspn .m ])
    → (h : CatIso C (cspn .r) (b))
    → (cspn .s₂ ≡ h .fst ⋆⟨ C ⟩ ϕ)
    → NatIso (F cspn) (F (ShiftCospanR cspn ϕ))
  FLiftIsoR {b} {cspn} ϕ (k , kiso) p =
    let η = λ {x → C .id ; y → C .id ; z → k} in
    record {
    trans = natTrans
      η
      (elimExpProp
      quiv (λ e → C .isSetHom _ _)
      (λ {f → C .⋆IdR _ ∙ sym (C .⋆IdL _) ; g → C .⋆IdR _ ∙ p})
      (λ {a} →
        cong (λ x → x ⋆⟨ C ⟩ (η a)) ((F cspn) .F-id {a}) ∙
        C .⋆IdL (η a) ∙
        sym (C .⋆IdR (η a)) ∙
        cong (λ x → η a ⋆⟨ C ⟩ x) (sym (F (ShiftCospanR cspn ϕ) .F-id {a}))
      )
      (λ {a} {_} {c} e1 e2 Fe1η≡ηsFe1 Fe2η≡ηsFe2 →
        cong (λ x → x ⋆⟨ C ⟩ (η c)) ((F cspn) .F-seq e1 e2) ∙
        C .⋆Assoc _ _ _ ∙
        cong (λ x → ((F cspn) ⟪ e1 ⟫) ⋆⟨ C ⟩ x) Fe2η≡ηsFe2 ∙
        sym (C .⋆Assoc _ _ _) ∙
        cong (λ x → x ⋆⟨ C ⟩ ((F (ShiftCospanR cspn ϕ)) ⟪ e2 ⟫)) Fe1η≡ηsFe1 ∙
        C .⋆Assoc _ _ _ ∙
        cong (λ x → (η a) ⋆⟨ C ⟩ x ) (sym ((F (ShiftCospanR cspn ϕ)) .F-seq e1 e2))
      )
      ) ;
    nIso =
      (λ { x → idCatIso .snd ; y → idCatIso .snd ; z → kiso })
    }
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

  -- separated for termination issues
  obTrans : {cspnFun : Cᴶ .ob} → (pb : Pullback C (Functor→Cospan cspnFun))
    → (NatTrans ((ΔPullback ^opF) ⟅ pb .pbOb ⟆) cspnFun)
  obTrans pb .N-ob x = pb .pbPr₁
  -- Could have equivalently defined this one with pb
  -- .pbPr₂ ⋆⟨ C ⟩ cspn .s₂
  -- but its a pullback so theyre the same
  obTrans {cspnFun} pb .N-ob y = pb .pbPr₁ ⋆⟨ C ⟩ (Functor→Cospan cspnFun) .s₁
  obTrans pb .N-ob z = pb .pbPr₂
  -- Goal of .N-hom ϕ
  -- (((ΔPullback ^opF) ⟅ pb .pbOb ⟆) .F-hom ϕ
  --        Cubical.Categories.NaturalTransformation.Base._.⋆ᴰ
  --        PullbackToRepresentable pb .element .N-ob y₁)
  --       ≡
  --       (PullbackToRepresentable pb .element .N-ob x₁
  --        Cubical.Categories.NaturalTransformation.Base._.⋆ᴰ F cpsn .F-hom ϕ)
  obTrans {cspnFun} pb .N-hom {a} {b} ϕ =
    let Δₐ = ((ΔPullback ^opF) ⟅ pb .pbOb ⟆) in
    elimExpProp quiv
    (λ e → C .isSetHom _ _)
    -- have naturality for f and g
    (λ {
      f → C .⋆IdL _ ;
      g → C .⋆IdL _ ∙ pb .pbCommutes
    })
    -- id is natural
    (λ {a} →
      cong (λ x → x ⋆⟨ C ⟩ obTrans pb .N-ob a) (Δₐ .F-id {a}) ∙
      C .⋆IdL (obTrans pb .N-ob a) ∙
      sym (C .⋆IdR (obTrans pb .N-ob a)) ∙
      cong (λ x → obTrans pb .N-ob a ⋆⟨ C ⟩ x) (sym (cspnFun .F-id {a}))
    )
    -- squares stack
    (λ {a} {_} {c} e1 e2 Δe1η≡ηFe1 Δe2η≡ηFe2 →
      cong (λ x → x ⋆⟨ C ⟩ (obTrans pb .N-ob c)) (Δₐ .F-seq e1 e2) ∙
      C .⋆Assoc _ _ _ ∙
      cong (λ x → (Δₐ ⟪ e1 ⟫) ⋆⟨ C ⟩ x) Δe2η≡ηFe2 ∙
      sym (C .⋆Assoc _ _ _) ∙
      cong (λ x → x ⋆⟨ C ⟩ (cspnFun ⟪ e2 ⟫)) Δe1η≡ηFe1 ∙
      C .⋆Assoc _ _ _ ∙
      cong (λ x → (obTrans pb .N-ob a) ⋆⟨ C ⟩ x ) (sym (cspnFun .F-seq e1 e2))
    )
    ϕ


  PullbackToRepresentable : ∀ {cspnFun} → Pullback C (Functor→Cospan cspnFun)
    → RightAdjointAt _ _ (ΔPullback) cspnFun
  PullbackToRepresentable pb .vertex = pb .pbOb
  PullbackToRepresentable pb .element = obTrans pb
  PullbackToRepresentable {cspn} pb .universal .coinduction η =
    pb .univProp (η .N-ob x) (η .N-ob z)
      (sym (η .N-hom (↑ f)) ∙ η .N-hom (↑ g))
      .fst .fst
  PullbackToRepresentable {cspnFun} pb .universal .commutes η =
    let univ = pb .univProp (η .N-ob x) (η .N-ob z)
                (sym (η .N-hom (↑ f)) ∙ η .N-hom (↑ g)) in
    makeNatTransPath (funExt (λ {
      x → sym (univ .fst .snd .fst) ;
      y → sym (C .⋆Assoc _ _ _) ∙
          cong (λ x → x ⋆⟨ C ⟩ cspnFun ⟪ ↑ f ⟫) (sym (univ .fst .snd .fst)) ∙
          sym (η .N-hom (↑ f)) ∙
          C .⋆IdL (η .N-ob y) ;
      z → sym (univ .fst .snd .snd)
    }))
  PullbackToRepresentable {cspn} pb .universal .is-uniq η =
    let univ = pb .univProp (η .N-ob x) (η .N-ob z)
                (sym (η .N-hom (↑ f)) ∙ η .N-hom (↑ g)) in
    λ f p → cong fst
      (sym (univ .snd
        ( f ,
          cong (λ a → a .N-ob x) (sym p) ,
          cong (λ a → a .N-ob z) (sym p)
        )
      ))

  module _ (pb : Pullbacks C) where
    PullbacksToUnivElts : RightAdjoint C Cᴶ (ΔPullback)
    PullbacksToUnivElts cspnFun = 
      PullbackToRepresentable (pb (Functor→Cospan cspnFun))

    PullbackF : Functor Cᴶ C
    PullbackF = ParamUnivElt→Functor _ _ _ PullbacksToUnivElts

    private
      module _ (a b c d : C .ob)
               (ϕ : C [ a , b ]) (ψ : C [ c , b ])
               (da : C [ d , a ]) (dc : C [ d , c ])
               (p : da ⋆⟨ C ⟩ ϕ ≡ dc ⋆⟨ C ⟩ ψ)
        where
        cspn : Cospan C
        cspn = cospan a b c ϕ ψ

        pback : C .ob
        pback = PullbackF .F-ob (F cspn)

        pbackPr₁ : C [ pback , a ]
        pbackPr₁ =  PullbacksToUnivElts (F cspn) .element .N-ob x

        pbackPr₂ : C [ pback , c ]
        pbackPr₂ =  PullbacksToUnivElts (F cspn) .element .N-ob z

        pbackCommutes : pbackPr₁ ⋆⟨ C ⟩ cspn .s₁ ≡ pbackPr₂ ⋆⟨ C ⟩ cspn .s₂
        pbackCommutes = sym (PullbacksToUnivElts (F cspn) .element .N-hom (↑ f))
          ∙ PullbacksToUnivElts (F cspn) .element .N-hom (↑ g)

        h : C [ d , pback ]
        h = pb _ .univProp da dc p .fst .fst

        hCommutesA : da ≡ (h ⋆⟨ C ⟩ pbackPr₁)
        hCommutesA = pb _ .univProp da dc p .fst .snd .fst

        hCommutesB : dc ≡ (h ⋆⟨ C ⟩ pbackPr₂)
        hCommutesB = pb _ .univProp da dc p .fst .snd .snd
