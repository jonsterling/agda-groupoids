{-# OPTIONS --without-K #-}

module Groupoid.Monoidal where

open import Agda.Primitive
module G where
  open import Groupoid public
    hiding (module Π)
  module Π where
    open Groupoid.Π public
    open import Groupoid.Bifunctor public
import Setoid as S
open import Type as T
  using (_,_)

record t {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  (A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ)
    : Set (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ) where
  no-eta-equality
  open G

  field
    ⊗ : Π.:⟨ A , A ⟩⇒₀ᵗ A
    𝟙 : obj A

  _⊗₀_
    : (a₀ a₁ : obj A) → obj A
  _⊗₀_ = λ a₀ a₁ → ⊗ Π.$₀ (a₀ , a₁)

  _⊗₁_
    : ∀ {a₀ a₁ a₂ a₃}
    → (f₀ : hom₀ A a₀ a₁)
    → (f₁ : hom₀ A a₂ a₃)
    → hom₀ A (a₀ ⊗₀ a₂) (a₁ ⊗₀ a₃)
  _⊗₁_ = λ f₀ f₁ → ⊗ Π.$₁ (f₀ , f₁)

  _⊗₂_
    : ∀ {a₀ a₁ a₂ a₃}
    → {f₀ g₀ : hom₀ A a₀ a₁}
    → {f₁ g₁ : hom₀ A a₂ a₃}
    → (p₀ : hom₁ A f₀ g₀)
    → (p₁ : hom₁ A f₁ g₁)
    → hom₁ A (f₀ ⊗₁ f₁) (g₀ ⊗₁ g₁)
  _⊗₂_ = λ p₀ p₁ → ⊗ Π.$₂ (p₀ , p₁)

  field
    ƛ
      : ∐.⟨ Π.!ᵍ 𝟙 [ ⊗ ],₀ - ⟩
      TF.⇔₁ ------------------ ≅₁
        -
    ρ
      : ∐.⟨ - [ ⊗ ],₀ Π.!ᵍ 𝟙 ⟩
      TF.⇔₁ ------------------ ≅₁
        -
    α
      : ∐.⟨ ⊗ [ ⊗ ]⊗₀ - ⟩
      TF.⇔₁ ------------- ≅₁
        ∐.⟨ - [ ⊗ ]⊗₀ ⊗ ⟩
        Π.∘₀ᵗ ∐.α

  field
    .tri
      : ∀ {a b} → hom₁ A
        ⊢ A [ idn₀ A ⊗₁ TF.₁⇒ ƛ {b} ∘₀ TF.₁⇒ α ]
        ---------------------------------------- ≃
        (TF.₁⇒ ρ {a} ⊗₁ idn₀ A)
    .pnt
      : ∀ {a b c d} → hom₁ A
        ⊢ A [ TF.₁⇒ α ∘₀ TF.₁⇒ α {((a ⊗₀ b) , c) , d} ]
        ----------------------------------------------- ≃
        ⊢ A [ idn₀ A ⊗₁ TF.₁⇒ α
     ∘₀ ⊢ A [ TF.₁⇒ α ∘₀ TF.₁⇒ α ⊗₁ idn₀ A ] ]
