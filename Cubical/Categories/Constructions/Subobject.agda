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

open import Cubical.Data.Sigma

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Morphism
open import Cubical.Categories.Limits.Pullback
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Cubical.Relation.Binary.Preorder
open import Cubical.Tactics.CategorySolver.Reflection

open import Cubical.Categories.Limits.Pullback.More

private
  variable
    ℓC ℓC' : Level

module _ (C : Category ℓC ℓC')  where

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

  open Pullback

  module _ (pb : Pullbacks C) where
    inducedMap : {X Y : C .ob} → (f : C [ X , Y ])
      → (SubObject Y) → (SubObject X)
    inducedMap {X} {Y} f [a↪y] = rec isSetSubObj
      (λ (A , (g , gmon)) →
        let cspn = (cospan X Y A f g) in
        let P = pb cspn in
         [ P .pbOb , (P .pbPr₁ , PBPreservesMonicL C cspn P gmon) ]ₛ
      )
      (λ (A , (g , gmon)) (B , (h , hmon)) ((k , kh≡g) , kiso) →
         let cspna = cospan X Y A f g in
         let cspnb = cospan X Y B f h in
         let univb = (pb cspnb .univProp
                        (pb cspna .pbPr₁ ⋆⟨ C ⟩ C .id)
                        (pb cspna .pbPr₂ ⋆⟨ C ⟩ k)
                        (
                          cong (λ x → x ⋆⟨ C ⟩ f) (C .⋆IdR (pb cspna .pbPr₁)) ∙
                          pb cspna .pbCommutes ∙
                          cong (λ x → pb cspna .pbPr₂ ⋆⟨ C ⟩ x) (sym kh≡g) ∙
                          sym (C .⋆Assoc _ _ _)
                        )
                     )
         in
         -- testing shiftcospan
         let _ = cspnb ≡⟨ refl ⟩ (PBRepresentable.ShiftCospanR C cspna h) ∎ in
         let X = preserveIsosF {_} {_} {_} {_} {_} {_} {PBRepresentable.PullbackF C pb}
                   (NatIso→FUNCTORIso
                     (PBRepresentable.IndexCat C) C
                       (PBRepresentable.FLiftIsoR C {B} {cspna} h (k , kiso) (sym kh≡g))
                   ) .snd
         in
         isEquivRel→effectiveIso isProp↪Iso isEquivRel↪Iso _ _ .Iso.inv (
           (univb .fst .fst , sym (univb .fst .snd .fst) ∙ C .⋆IdR _) ,
           isiso (X .inv) {!X .sec!} {! X .ret!})
           {-
           preserveIsosF {_} {_} {_} {_} {_} {_} {PBRepresentable.PullbackF C pb}
             (NatIso→FUNCTORIso
               (PBRepresentable.IndexCat C) C
               (PBRepresentable.FLiftIsoR C h (k , kiso) (sym kh≡g))
              ) .snd)
          -}
      ) [a↪y]
