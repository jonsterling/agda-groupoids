{-# OPTIONS --without-K #-}

module Groupoid.Closed where

open import Agda.Primitive
module G where
  open import Groupoid public
    hiding (module Π; module TF)
  module Π where
    open Groupoid.Π public
    open import Groupoid.Bifunctor public
    open import Groupoid.Presheaf public
    open import Groupoid.Profunctor public
  module TF where
    open Groupoid.TF public
    open import Groupoid.Dinatural public
import Setoid as S
open import Type as T
  using (_,_)

record t {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  (A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ)
    : Set (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ) where
  no-eta-equality
  open G
  open TF
  open ∐

  field
    ⊸ : A Π.:[ A ]⇏₀ᵗ A
    𝟙 : obj A

  _⊸₀_
    : (a₀ : obj A)
    → (a₁ : obj A)
    → obj A
  _⊸₀_ = λ a₀ a₁ → ⊸ Π.$₀ (a₀ , a₁)

  _⊸₁_
    : ∀ {a₀ a₁ a₂ a₃}
    → (f₀ : hom₀ A a₁ a₀)
    → (f₁ : hom₀ A a₂ a₃)
    → hom₀ A (a₀ ⊸₀ a₂) (a₁ ⊸₀ a₃)
  _⊸₁_ = λ f₀ f₁ → ⊸ Π.$₁ (f₀ , f₁)

  ._⊸₂_
    : ∀ {a₀ a₁ a₂ a₃}
    → {f₀ f₁ : hom₀ A a₁ a₀}
    → {g₀ g₁ : hom₀ A a₂ a₃}
    → (p₀ : hom₁ A f₀ f₁)
    → (p₁ : hom₁ A g₀ g₁)
    → hom₁ A (f₀ ⊸₁ g₀) (f₁ ⊸₁ g₁)
  _⊸₂_ = λ p₀ p₁ → ⊸ Π.$₂ (p₀ , p₁)

  lazy : A Π.⇒₀ᵗ A
  lazy = ⟨ Π.!ᵍ 𝟙 [ ⊸ ],₀ - ⟩

  dual : A Π.⇏₀ᵗ A
  dual = ⟨ - [ ⊸ ],₀ Π.!ᵍ 𝟙 ⟩

  field
    susp : - ⇔₁ᵗ lazy
    idn : Π.!:[ A ]₀ 𝟙 :⇏₁ᵗ ⊸
