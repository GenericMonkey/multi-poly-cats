{-# OPTIONS --safe #-}
module Cubical.Tactics.CategorySolver.Examples where

open import Cubical.Foundations.Prelude hiding (≡⟨⟩-syntax; _≡⟨_⟩_)

open import Cubical.Categories.Category
open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓ ℓ' : Level

≡⟨⟩-syntax : ∀ {ℓ} {A : Type ℓ} (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨⟩-syntax x q p = p ∙ q

infixr 2 ≡⟨⟩-syntax
-- infix  3 _∎

syntax ≡⟨⟩-syntax x q p = x ≡⟨ p ⟩ q

-- _∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
-- x ∎ = refl

module Examples (𝓒 : Category ℓ ℓ') where
  open Category 𝓒

  _ : ∀ {A} → id {A} ≡ id {A}
  _ = solveCat! 𝓒

  _ : ∀ {A B}{f : 𝓒 [ A , B ]} → f ∘ id ≡ f
  _ = solveCat! 𝓒

  _ : ∀ {A B}{f : 𝓒 [ A , B ]} → id ∘ (id ∘ id ∘ f) ∘ id ≡ id ∘ id ∘ (id ∘ f)
  _ = solveCat! 𝓒

  _ : ∀ {A B C}{f : 𝓒 [ A , B ]}{g : 𝓒 [ B , C ]} → f ⋆ g ≡ g ∘ (id ∘ f) ∘⟨ 𝓒 ⟩ id
  _ = solveCat! 𝓒

  ex : ∀ {A B C}(f : 𝓒 [ A , B ])(g : 𝓒 [ B , C ])(h : 𝓒 [ A , C ])
    → (f ⋆ (id ⋆ g)) ≡ h
    → f ⋆ g ≡ h ⋆ id
  ex f g h p =
    f ⋆ g ≡⟨ solveCat! 𝓒 ⟩
    (f ⋆ (id ⋆ g)) ≡⟨ p ⟩
    h ≡⟨ solveCat! 𝓒 ⟩
    h ⋆ id ∎
