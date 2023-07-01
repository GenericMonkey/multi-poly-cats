{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Subobject where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Logic

open import Cubical.HITs.SetQuotients renaming ([_] to [_]ₛ)
open import Cubical.HITs.PropositionalTruncation renaming
  (rec to recp ; rec2 to rec2p)

open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Data.Graph.Base
open import Cubical.Data.Sigma

open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Instances.Cospan

open import Cubical.Categories.Adjoint.UniversalElements

open import Cubical.Categories.Constructions.Free.Category
   renaming (rec to recCat)
open import Cubical.Categories.Constructions.BinProduct

open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Morphism
open import Cubical.Categories.Limits.Pullback
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Relation.Binary.Preorder
open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓ' : Level
    A : Type ℓ'
    R : A → A → Type ℓ'

module _ {ℓC ℓC' : Level} (C : Category ℓC ℓC')  where

  open Category

  -↪_ : (C .ob) → Type _
  -↪ X  = Σ[ A ∈ C .ob ] (Σ[ f ∈ C [ A , X ] ] isMonic C f)

  -- preorder is the existence of a morphism between domains
  -- that commutes with monic morphisms
  _≤↪_ : {X : C .ob} → -↪ X → -↪ X → hProp _
  (a , (f , _)) ≤↪ (b , (g , gMon)) =
    (Σ[ k ∈ C [ a , b ] ] k ⋆⟨ C ⟩ g ≡ f) ,
    -- functions equal because of g being monic
    -- equalities equal because HomSets are sets
    λ (p , pg≡f) (q , qg≡f) →  ΣPathP (
      let p≡q = gMon (pg≡f ∙ (sym qg≡f)) in
        p≡q ,
        isProp→PathP (λ i → C .isSetHom (p≡q i ⋆⟨ C ⟩ g) f) _ _
    )

  open BinaryRelation

  -- refl due to identity
  isRefl≤↪ : {X : C .ob} → isRefl( (λ a b →  ⟨ _≤↪_ {X} a b ⟩ ) )
  isRefl≤↪ = (λ (_ , (f , _)) → (C .id) , C .⋆IdL f)

  -- trans is just composition
  isTrans≤↪ : {X : C .ob} → isTrans( (λ a b →  ⟨ _≤↪_ {X} a b ⟩) )
  isTrans≤↪ =
        (λ _ _ (_ , (h , _))
          (p , pg≡f) (q , qh≡g) →  p ⋆⟨ C ⟩ q ,
            C .⋆Assoc p q h ∙
            (congS (λ ϕ → p ⋆⟨ C ⟩ ϕ) qh≡g) ∙
            pg≡f
        )

  MonoPreorder : (C .ob) → Preorder _ _
  MonoPreorder X =
    -- objects are monic morphisms into X
    -↪ X ,
    preorderstr
      (λ a b → ⟨ a ≤↪ b ⟩ )
      (ispreorder
        (λ a b → str (a ≤↪ b))
        (isRefl≤↪ {X})
        (isTrans≤↪ {X})
      )

  ↪Iso : {X : C .ob} → -↪ X → -↪ X → Type _
  ↪Iso a↪x b↪x = Σ[ k ∈ ⟨ a↪x ≤↪ b↪x ⟩ ] isIsoC C (k .fst)


  isProp↪Iso : {X : C .ob} → (a↪x : -↪ X) → (b↪x : -↪ X)
    → isProp (↪Iso a↪x b↪x)
  isProp↪Iso a↪x b↪x = isPropΣ (str (a↪x ≤↪ b↪x)) λ _ → isPropIsIso _

  isRefl↪Iso : {X : C .ob} → isRefl(↪Iso {X})
  isRefl↪Iso =
    λ a↪x → isRefl≤↪ a↪x , isiso (C .id) (C .⋆IdL (C .id)) (C .⋆IdL (C .id))

  open isIsoC

  isTrans↪Iso : {X : C .ob} → isTrans(↪Iso {X})
  isTrans↪Iso = λ a↪x b↪x c↪x abi bci →
    isTrans≤↪ a↪x b↪x c↪x (abi .fst) (bci .fst) ,
    isiso (bci .snd .inv ⋆⟨ C ⟩ abi .snd .inv)
      ( ((bci .snd .inv ⋆⟨ C ⟩ abi .snd .inv) ⋆⟨ C ⟩
        (isTrans≤↪ a↪x b↪x c↪x (abi .fst) (bci .fst) .fst)
          ≡⟨ solveCat! C ⟩
        (bci .snd .inv) ⋆⟨ C ⟩
        ((abi .snd .inv ⋆⟨ C ⟩ abi .fst .fst) ⋆⟨ C ⟩ (bci .fst .fst)) ∎)
        ∙
        cong (λ x → bci .snd .inv ⋆⟨ C ⟩ (x ⋆⟨ C ⟩ (bci .fst .fst)))
          (abi .snd .sec)
        ∙
        cong (λ x → bci .snd .inv ⋆⟨ C ⟩ x) (C .⋆IdL (bci .fst .fst))
        ∙
        bci .snd .sec
      )
      (  ((isTrans≤↪ a↪x b↪x c↪x (abi .fst) (bci .fst) .fst) ⋆⟨ C ⟩
         ((bci .snd .inv) ⋆⟨ C ⟩ (abi .snd .inv))
           ≡⟨ solveCat! C ⟩
         (abi .fst .fst) ⋆⟨ C ⟩
         (((bci .fst .fst) ⋆⟨ C ⟩ (bci .snd .inv)) ⋆⟨ C ⟩ (abi .snd .inv)) ∎)
        ∙
        cong (λ x → abi .fst .fst ⋆⟨ C ⟩ (x ⋆⟨ C ⟩ (abi .snd .inv)))
          (bci .snd .ret)
        ∙
        cong (λ x → abi .fst .fst ⋆⟨ C ⟩ x) (C .⋆IdL (abi .snd .inv))
        ∙
        abi .snd .ret
      )

  isSym↪Iso : {X : C .ob} → isSym (↪Iso {X})
  isSym↪Iso a↪x b↪x abi =
    ( abi .snd .inv ,
      cong (λ x → (abi .snd .inv) ⋆⟨ C ⟩ x) (sym (abi .fst .snd))
      ∙
      sym (C .⋆Assoc _ _ _)
      ∙
      cong (λ x → x ⋆⟨ C ⟩ (b↪x .snd .fst)) (abi .snd .sec)
      ∙
      C .⋆IdL (b↪x .snd .fst)
    )  ,
    isiso (abi .fst .fst) (abi .snd .ret) (abi .snd .sec)

  isEquivRel↪Iso : {X : C .ob} → isEquivRel (↪Iso {X})
  isEquivRel↪Iso = equivRel isRefl↪Iso isSym↪Iso isTrans↪Iso



  SubObject : (C .ob) → Type _
  SubObject X = (-↪ X) / ↪Iso

  _≤[↪]_ : {X : C .ob} → (SubObject X) → (SubObject X) → hProp _
  [a↪x] ≤[↪] [b↪x] = rec2 isSetHProp _≤↪_
    (λ a b c abi →
      ⇔toPath
        (λ y →  abi .snd .inv ⋆⟨ C ⟩ y .fst ,
          C .⋆Assoc _ _ _ ∙
          cong (λ v → abi .snd .inv ⋆⟨ C ⟩ v) (y .snd) ∙
          isSym↪Iso a b abi .fst .snd
        )
        (λ z → abi .fst .fst ⋆⟨ C ⟩ z .fst ,
          C .⋆Assoc _ _ _ ∙
          cong (λ v → abi .fst .fst ⋆⟨ C ⟩ v) (z .snd) ∙
          abi .fst .snd
        )
    )
    (λ a b c bci →
      ⇔toPath
        (λ y →  y .fst ⋆⟨ C ⟩ bci .fst .fst ,
          C .⋆Assoc _ _ _  ∙
            (cong (λ v → y .fst ⋆⟨ C ⟩ v) (bci .fst .snd)) ∙ y .snd)
        (λ z → z .fst ⋆⟨ C ⟩ bci .snd .inv ,
          C .⋆Assoc _ _ _ ∙ cong (λ v → z .fst ⋆⟨ C ⟩ v)
            (isSym↪Iso b c bci .fst .snd) ∙ z .snd
        )
    )
    [a↪x] [b↪x]

  isRefl≤[↪] : {X : C .ob} → isRefl( (λ a b →  ⟨ _≤[↪]_ {X} a b ⟩ ) )
  isRefl≤[↪] = elimProp
    (λ [a↪x] → str ([a↪x] ≤[↪] [a↪x]))
    isRefl≤↪

  isTrans≤[↪] : {X : C .ob} → isTrans( (λ a b →  ⟨ _≤[↪]_ {X} a b ⟩ ) )
  isTrans≤[↪] = elimProp3
    (λ [a↪x] [b↪x] [c↪x] → isProp→ (isProp→ (str ([a↪x] ≤[↪] [c↪x]))))
    isTrans≤↪

  isSetSubObj : {X : C .ob} → isSet (SubObject X)
  isSetSubObj = squash/

  isAntisym≤[↪] : {X : C .ob} → isAntisym( (λ a b →  ⟨ _≤[↪]_ {X} a b ⟩ ) )
  isAntisym≤[↪] = λ [a] [b] [a]≤[b] [b]≤[a] → rec2p
    {-
      Proof by recursion on propositional truncation. []surjective gives us
      existence of an underlying mono a and b such that [ a ] = [a] and
      [ b ] = [b]. We stitch these paths along with a proof that [ a ] = [ b ]
      , which is the direct proof that the 2 morphisms back and forth form
      an isomorphism between a and b.
    -}
    (isSetSubObj [a] [b])
    (λ (a , arep) (b , brep) →
      let
        -- [a]≤[b] → [ a ] ≤ [ b ]
        (k , kb≡a) = transport
          (sym ((cong (λ x → ⟨ [ a ]ₛ ≤[↪] x ⟩) brep) ∙
          (cong (λ x → ⟨ x ≤[↪] [b] ⟩) arep)))
          [a]≤[b]
        -- [b]≤[a] → [ b ] ≤ [ a ]
        (j , ja≡b) = transport
          (sym ((cong (λ x → ⟨ x ≤[↪] [ a ]ₛ ⟩) brep) ∙
          (cong (λ x → ⟨ [b] ≤[↪] x ⟩) arep)))
          [b]≤[a]
      in
      (sym arep) ∙
      ((isEquivRel→effectiveIso isProp↪Iso isEquivRel↪Iso) a b .Iso.inv
        ((k , kb≡a) ,
        isiso
          j
          (b .snd .snd
            (C .⋆Assoc _ _ _ ∙
            (cong (λ z → j ⋆⟨ C ⟩ z) kb≡a) ∙
            ja≡b ∙
            sym (C .⋆IdL (b .snd .fst)))
          )
          (a .snd .snd
            (C .⋆Assoc _ _ _ ∙
            cong (λ z → k ⋆⟨ C ⟩ z) ja≡b ∙
            kb≡a ∙
            sym (C .⋆IdL (a .snd .fst)))
          )
        )
      ) ∙
      brep
    )
    ([]surjective [a]) ([]surjective [b])

  SubObjPoset : (C .ob) → Poset _ _
  SubObjPoset X =
    -- objects are the subobjects
    (SubObject X) ,
    (posetstr
      (λ a b → ⟨ a ≤[↪] b ⟩ )
      (isposet
        isSetSubObj
        ((λ a b → str (a ≤[↪] b ) ))
        isRefl≤[↪]
        isTrans≤[↪]
        isAntisym≤[↪]
      )
    )

  open Cospan
  open Pullback

  PBPreservesMonicL : {C : Category ℓC ℓC'} →
    (cspn : Cospan C) → (pb : Pullback C cspn)
    → isMonic C (cspn .s₂)
    → isMonic C (pb .pbPr₁)
  PBPreservesMonicL {C} cspn pb s2mon {_} {a} {a'} =
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
  PBPreservesMonicR : {C : Category ℓC ℓC'} →
    (cspn : Cospan C) → (pb : Pullback C cspn)
    → isMonic C (cspn .s₁)
    → isMonic C (pb .pbPr₂)
  PBPreservesMonicR {C} cspn pb s1mon =
    PBPreservesMonicL {C}
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

  module _ (pb : Pullbacks C) where
    inducedMap : {X Y : C .ob} → (f : C [ X , Y ])
      → (SubObject Y) → (SubObject X)
    inducedMap {X} {Y} f [a↪y] = rec isSetSubObj
      (λ (A , (g , gmon)) →
        let cspn = (cospan X Y A f g) in
        let P = pb cspn in
         [ P .pbOb , (P .pbPr₁ , PBPreservesMonicL {C} cspn P gmon) ]ₛ
      )
      (λ (A , (g , gmon)) (B , (h , hmon)) ((k , kh≡g) , kiso) → {!  !} ) [a↪y]

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

  -- open FreeCategory graph

  IndexCat : Category ℓ-zero (ℓ-suc ℓ-zero)
  IndexCat = FreeCat quiv

  -- _ : IndexCat [ z , y ]
  -- _ = (↑ g) ⋆ₑ idₑ


  -- IndexCat : Category ℓ-zero ℓ-zero
  -- IndexCat = CospanCat

  Cᴶ : Category _ _
  Cᴶ = FUNCTOR IndexCat C

  open Functor

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

  -- F cspn .F-ob ⓪ = cspn .l
  -- F cspn .F-ob ① = cspn .m
  -- F cspn .F-ob ② = cspn .r
  -- F cspn .F-hom {⓪}{①} tt = cspn .s₁
  -- F cspn .F-hom {②}{①} tt = cspn .s₂
  -- F cspn .F-hom {②}{②} tt = C .id
  -- F cspn .F-hom {①}{①} tt = C .id
  -- F cspn .F-hom {⓪}{⓪} tt = C .id
  -- F cspn .F-id {⓪} = refl
  -- F cspn .F-id {①} = refl
  -- F cspn .F-id {②} = refl
  -- F cspn .F-seq ϕ ψ = {!!}

  PullbackToRepresentable : ∀ {cspn} → Pullback C cspn
    → RightAdjointAt _ _ (ΔPullback) (F cspn)
  PullbackToRepresentable pb .vertex = pb .pbOb
  -- PullbackToRepresentable pb .element = {!!}
  PullbackToRepresentable {cspn} pb .element .N-ob x = pb .pbPr₁

  -- Could have equivalently defined this one with pb
  -- .pbPr₂ ⋆⟨ C ⟩ cspn .s₂
  -- but its a pullback so theyre the same
  PullbackToRepresentable {cspn} pb .element .N-ob y = pb .pbPr₁ ⋆⟨ C ⟩ cspn .s₁
  PullbackToRepresentable {cspn} pb .element .N-ob z = pb .pbPr₂

  -- TODO it seems like here we need to pattern match over morphisms in IndexCat
  PullbackToRepresentable {cspn} pb .element .N-hom {a} {b} ϕ =
    let Δₐ = ((ΔPullback ^opF) ⟅ PullbackToRepresentable pb .vertex ⟆) in
    let η = PullbackToRepresentable pb .element .N-ob in
    elimExpProp quiv
    {P = λ {k} {j} e →
      (Δₐ ⟪ e ⟫) ⋆⟨ C ⟩ (η j) ≡ (η k) ⋆⟨ C ⟩ ((F cspn) ⟪ e ⟫)
    }
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
  PullbackToRepresentable pb .universal = {!!}
