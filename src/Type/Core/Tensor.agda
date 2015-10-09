{-# OPTIONS --without-K #-}

module Type.Core.Tensor where

open import Agda.Primitive
import Type.Core.Exponential as Π
open import Type.Core.Tensor.Boot public

⟨_,_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {X : Set ℓ₀} {A : X → Set ℓ₁} {B : ∀ {x} → A x → Set ℓ₂}
  → (F : Π.t X A)
  → (G : Π.t X (λ x → B (F x)))
  → (Π.t X (λ x → t (A x) B))
⟨ F , G ⟩ x = F x , G x

⟨_⊗_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
  → {X₀ : Set ℓ₀} {X₁ : X₀ → Set ℓ₁} {A : Set ℓ₂} {B : A → Set ℓ₃}
  → (F : X₀ Π.⇒₀ A)
  → (G : ∀ {x₀} → X₁ x₀ Π.⇒₀ B (F x₀))
  → (t X₀ X₁ Π.⇒₀ t A B)
⟨ F ⊗ G ⟩ (x , y) = F x , G y
