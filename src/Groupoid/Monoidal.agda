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
  field
    ⊗ : G.Π.:⟨ A , A ⟩⇒₀ᵗ A
    𝟙 : G.obj A

  _⊗₀_
    : (a₀ a₁ : G.obj A) → G.obj A
  _⊗₀_ = λ a₀ a₁ → ⊗ G.Π.$₀ (a₀ , a₁)

  _⊗₁_
    : ∀ {a₀ a₁ a₂ a₃}
    → (f₀ : G.hom₀ A a₀ a₁)
    → (f₁ : G.hom₀ A a₂ a₃)
    → G.hom₀ A (a₀ ⊗₀ a₂) (a₁ ⊗₀ a₃)
  _⊗₁_ = λ f₀ f₁ → ⊗ G.Π.$₁ (f₀ , f₁)

  _⊗₂_
    : ∀ {a₀ a₁ a₂ a₃}
    → {f₀ g₀ : G.hom₀ A a₀ a₁}
    → {f₁ g₁ : G.hom₀ A a₂ a₃}
    → (p₀ : G.hom₁ A f₀ g₀)
    → (p₁ : G.hom₁ A f₁ g₁)
    → G.hom₁ A (f₀ ⊗₁ f₁) (g₀ ⊗₁ g₁)
  _⊗₂_ = λ p₀ p₁ → ⊗ G.Π.$₂ (p₀ , p₁)

  field
    ƛ
      : ⊗ G.Π.∘₀ᵗ G.∐.⟨ G.Π.!ᵍ 𝟙 ,₀ G.Π.idn₀* ⟩
      G.TF.⇔₁ --------------------------------------- ≅₁
        G.Π.idn₀*
    ρ
      : G.Π.idn₀*
      G.TF.⇔₁ --------------------------------------- ≅₁
        ⊗ G.Π.∘₀ᵗ G.∐.⟨ G.Π.idn₀* ,₀ G.Π.!ᵍ 𝟙 ⟩
  --   α
  --     : ⊗ G.Π.∘₀ᵗ G.∐.⟨ ⊗ ⊗₀ G.Π.idn₀* ⟩
  --     G.TF.⇔₁ --------------------------------- ≅₁
  --       (⊗ G.Π.∘₀ᵗ G.∐.⟨ G.Π.idn₀* ⊗₀ ⊗ ⟩
  --          G.Π.∘₀ᵗ {!!})
  -- field
  --   .tri
  --     : ∀ {a₀ a₁ : G.obj A} → G.hom₁ A
  --       G.⊢ A [ G.idn₀ A ⊗₁ G.TF.₁⇒ ƛ ∘₀ G.TF.₁⇒ α ]
  --       ------------------------------------------------- ≃
  --       (G.TF.₁⇒ ρ ⊗₁ G.idn₀ A)
  --   .pnt
  --     : ∀ {a₀ a₁ a₂ a₃ : G.obj A} → G.hom₁ A
  --       G.⊢ A [ G.TF.₁⇒ α ∘₀ G.TF.₁⇒ α ]
  --       -------------------------------- ≃
  --       G.⊢ A [ G.idn₀ A ⊗₁ G.TF.₁⇒ α
  --    ∘₀ G.⊢ A [ G.TF.₁⇒ α
  --    ∘₀         G.TF.₁⇒ α ⊗₁ G.idn₀ A ] ]
