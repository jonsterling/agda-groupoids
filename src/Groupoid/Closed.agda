{-# OPTIONS --without-K #-}

module Groupoid.Closed where

open import Agda.Primitive
module G where
  open import Groupoid public
    hiding (module Map)
  module I where
    module SETOID where
      open import Groupoid.Instances.SETOID public
  module Map where
    open Groupoid.Map public
    open import Groupoid.Bifunctor public
    open import Groupoid.Presheaf public
    open import Groupoid.Profunctor public
    open import Groupoid.Dinatural public
import Setoid as S
open import Type as T
  using (_,_)

record t {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  (A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ)
    : Set (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ) where
  no-eta-equality
  open G hiding
    (idn₀; cmp₀)
  open Map hiding
    (idn; cmp)
  open Ten

  field
    ⊸ : A :[ A ]⇏₀ᵗ A
    𝟙 : obj A

  _⊸₀_
    : (a₀ : obj A)
    → (a₁ : obj A)
    → obj A
  _⊸₀_ = λ a₀ a₁ → ⊸ $₀ (a₀ , a₁)

  _⊸₁_
    : ∀ {a₀ a₁ a₂ a₃}
    → (f : hom₀ A a₁ a₀)
    → (g : hom₀ A a₂ a₃)
    → hom₀ A (a₀ ⊸₀ a₂) (a₁ ⊸₀ a₃)
  _⊸₁_ = λ f g → ⊸ $₁ (f , g)

  ._⊸₂_
    : ∀ {a₀ a₁ a₂ a₃}
    → {f₀ f₁ : hom₀ A a₁ a₀}
    → {g₀ g₁ : hom₀ A a₂ a₃}
    → (p₀ : hom₁ A f₀ f₁)
    → (p₁ : hom₁ A g₀ g₁)
    → hom₁ A (f₀ ⊸₁ g₀) (f₁ ⊸₁ g₁)
  _⊸₂_ = λ p₀ p₁ → ⊸ $₂ (p₀ , p₁)

  lazy : A ⇒₀ᵗ A
  lazy = ⟨ !ᵍ 𝟙 [ ⊸ ],₀ - ⟩

  dual : A ⇏₀ᵗ A
  dual = ⟨ - [ ⊸ ],₀ !ᵍ 𝟙 ⟩

  field
    susp
      : -
      ⇔₁ᵗ -- ≅₁
       lazy
    idn
      : !:[ A ]₀ 𝟙
      :⇏₁ᵗ -------
        ⊸
    cmp
      : 𝝀 (⟨ - [ ⊸ ]⊗₀ - ⟩ ∘₀ᵗ π₁)
      :⇏₁ᵗ ---------------------------------------------------
        𝝀 ⟨ ⟨ π₁ [ Op:⇏ ⊸ ]⊗₀ π₀ ⟩ [ ⊸ ],₀ ⟨ π₀ [ ⊸ ]⊗₀ π₁ ⟩ ⟩

  ♯ : ∀ {a} → hom₀ A a (𝟙 ⊸₀ a)
  ♯ = ⟨ susp ⇔⟩₁

  ♭ : ∀ {a} → hom₀ A (𝟙 ⊸₀ a) a
  ♭ = ⟨⇔ susp ⟩₁

  idn₀ : ∀ {a} → hom₀ A 𝟙 (a ⊸₀ a)
  idn₀ = :com₁ idn

  cmp₀ : ∀ {a b c} → hom₀ A (b ⊸₀ c) ((a ⊸₀ b) ⊸₀ (a ⊸₀ c))
  cmp₀ {a}{b}{c} = com₁ (:com₁ cmp {a}) {b , c}

  field
    .coh₀
      : ∀ {a b}
      → hom₁ A
          {𝟙}
          {(a ⊸₀ b) ⊸₀ (a ⊸₀ b)}
      ⊢ A [ cmp₀ ∘₀ idn₀ ]
      -------------------- ≃₁
      idn₀

    .coh₁
      : ∀ {a b}
      → hom₁ A
          {a ⊸₀ b}
          {𝟙 ⊸₀ (a ⊸₀ b)}
      ⊢ A [ (idn₀ ⊸₁ G.idn₀ A) ∘₀ cmp₀ ]
      ---------------------------------- ≃₁
      ♯

    .coh₂
      : ∀ {b c}
      → hom₁ A
          {b ⊸₀ c}
          {b ⊸₀ (𝟙 ⊸₀ c)}
      ⊢ A [ (♯ ⊸₁ G.idn₀ A) ∘₀ cmp₀ ]
      ------------------------------- ≃₁
      (G.idn₀ A ⊸₁ ♯)

    .coh₃
      : ∀ {a b c d}
      → hom₁ A
          {c ⊸₀ d}
          {(b ⊸₀ c) ⊸₀ ((a ⊸₀ b) ⊸₀ (a ⊸₀ d))}
      ⊢ A [ (G.idn₀ A ⊸₁ cmp₀) ∘₀ cmp₀ ]
      ------------------------------------------------- ≃₁
      ⊢ A [ (cmp₀ ⊸₁ G.idn₀ A) ∘₀ ⊢ A [ cmp₀ ∘₀ cmp₀ ] ]

    .coh₄
      : ∀ {a b}
      → hom₀ (I.SETOID.g d _ _) (homˢ A (a , b)) (homˢ A (𝟙 , a ⊸₀ b))
