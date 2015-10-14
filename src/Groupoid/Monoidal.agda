{-# OPTIONS --without-K #-}

module Groupoid.Monoidal where

open import Agda.Primitive
private
  module G where
    open import Groupoid public
      hiding (module Map)
    module Map where
      open Groupoid.Map public
      open import Groupoid.Bifunctor public
import Setoid as S
open import Type as T
  using (_,_)

record t {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  (A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ)
    : Set (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ) where
  no-eta-equality
  open G
  open Map

  field
    ⊗ : Map.:⟨ A , A ⟩⇒₀ᵗ A
    𝟙 : obj A

  _⊗₀_
    : (a₀ a₁ : obj A) → obj A
  _⊗₀_ = λ a₀ a₁ → ⊗ Map.$₀ (a₀ , a₁)

  _⊗₁_
    : ∀ {a₀ a₁ a₂ a₃}
    → (f : hom₀ A a₀ a₁)
    → (g : hom₀ A a₂ a₃)
    → hom₀ A (a₀ ⊗₀ a₂) (a₁ ⊗₀ a₃)
  _⊗₁_ = λ f g → ⊗ Map.$₁ (f , g)

  ._⊗₂_
    : ∀ {a₀ a₁ a₂ a₃}
    → {f₀ f₁ : hom₀ A a₀ a₁}
    → {g₀ g₁ : hom₀ A a₂ a₃}
    → (p₀ : hom₁ A f₀ f₁)
    → (p₁ : hom₁ A g₀ g₁)
    → hom₁ A (f₀ ⊗₁ g₀) (f₁ ⊗₁ g₁)
  _⊗₂_ = λ p₀ p₁ → ⊗ Map.$₂ (p₀ , p₁)

  field
    ƛ
      : Ten.⟨ Map.!ᵍ 𝟙 [ ⊗ ],₀ - ⟩
      ⇔₁ᵗ ------------------------ ≅₁
        -
    ρ
      : Ten.⟨ - [ ⊗ ],₀ Map.!ᵍ 𝟙 ⟩
      ⇔₁ᵗ ------------------------ ≅₁
        -
    α
      : Ten.⟨ ⊗ [ ⊗ ]⊗₀ - ⟩
      ⇔₁ᵗ ----------------- ≅₁
        Ten.⟨ - [ ⊗ ]⊗₀ ⊗ ⟩ Map.∘₀ᵗ Ten.α

  field
    .tri
      : ∀ {a₀ a₁}
      → hom₁ A
          {(a₀ ⊗₀ 𝟙) ⊗₀ a₁}
          {a₀ ⊗₀ a₁}
      ⊢ A [ (idn₀ A ⊗₁ ⟨ ƛ ⇔⟩₁) ∘₀ ⟨ α ⇔⟩₁ ]
      -------------------------------------- ≃₁
      (⟨ ρ ⇔⟩₁ ⊗₁ idn₀ A)

    .pnt
      : ∀ {a₀ a₁ a₂ a₃}
      → hom₁ A
          {((a₀ ⊗₀ a₁) ⊗₀ a₂) ⊗₀ a₃}
          {a₀ ⊗₀ (a₁ ⊗₀ (a₂ ⊗₀ a₃))}
      ⊢ A [ ⟨ α ⇔⟩₁ ∘₀ ⟨ α ⇔⟩₁ ]
      -------------------------- ≃₁
      ⊢ A [ (idn₀ A ⊗₁ ⟨ α ⇔⟩₁) ∘₀ ⊢ A [ ⟨ α ⇔⟩₁ ∘₀ (⟨ α ⇔⟩₁ ⊗₁ idn₀ A) ] ]
