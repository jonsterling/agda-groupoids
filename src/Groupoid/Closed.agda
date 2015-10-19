{-# OPTIONS --without-K #-}

module Groupoid.Closed where

open import Agda.Primitive
module G where
  open import Groupoid public
    hiding (module Map)
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
  open G
  open Map using (_∘₀ᵗ_)
  open Ten

  field
    ⊸ : A Map.:[ A ]⇏₀ᵗ A
    𝟙 : obj A

  _⊸₀_
    : (a₀ : obj A)
    → (a₁ : obj A)
    → obj A
  _⊸₀_ = λ a₀ a₁ → ⊸ Map.$₀ (a₀ , a₁)

  _⊸₁_
    : ∀ {a₀ a₁ a₂ a₃}
    → (f : hom₀ A a₁ a₀)
    → (g : hom₀ A a₂ a₃)
    → hom₀ A (a₀ ⊸₀ a₂) (a₁ ⊸₀ a₃)
  _⊸₁_ = λ f g → ⊸ Map.$₁ (f , g)

  ._⊸₂_
    : ∀ {a₀ a₁ a₂ a₃}
    → {f₀ f₁ : hom₀ A a₁ a₀}
    → {g₀ g₁ : hom₀ A a₂ a₃}
    → (p₀ : hom₁ A f₀ f₁)
    → (p₁ : hom₁ A g₀ g₁)
    → hom₁ A (f₀ ⊸₁ g₀) (f₁ ⊸₁ g₁)
  _⊸₂_ = λ p₀ p₁ → ⊸ Map.$₂ (p₀ , p₁)

  lazy : A Map.⇒₀ᵗ A
  lazy = ⟨ Map.!ᵍ 𝟙 [ ⊸ ],₀ - ⟩

  dual : A Map.⇏₀ᵗ A
  dual = ⟨ - [ ⊸ ],₀ Map.!ᵍ 𝟙 ⟩

  field
    susp
      : - Map.⇔₁ᵗ lazy
    idn
      : Map.!:[ A ]₀ 𝟙 Map.:⇏₁ᵗ ⊸
    cmp
      : Map.𝝀 (⟨ - [ ⊸ ]⊗₀ - ⟩ ∘₀ᵗ π₁)
      Map.:⇏₁ᵗ
        Map.𝝀 ⟨ ⟨ π₁ [ Op.⇒ ⊸ ∘₀ᵗ Op.⊗ ]⊗₀ π₀ ⟩ [ ⊸ ],₀ ⟨ π₀ [ ⊸ ]⊗₀ π₁ ⟩ ⟩
