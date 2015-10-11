{-# OPTIONS --without-K #-}

module Type.Core.Tensor where

open import Agda.Primitive
import Type.Core.Hom as Π
open import Type.Core.Tensor.Boot public

⟨_,_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {X : Set ℓ₀} {A : Set ℓ₁} {B : Set ℓ₂}
  → (F : X Π.⇒₀ A)
  → (G : X Π.⇒₀ B)
  → (X Π.⇒₀ A ⊗ B)
⟨ F , G ⟩ x = F x , G x

⟨_⊗_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
  → {X₀ : Set ℓ₀} {X₁ : Set ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃}
  → (F : X₀ Π.⇒₀ A)
  → (G : X₁ Π.⇒₀ B)
  → (X₀ ⊗ X₁ Π.⇒₀ A ⊗ B)
⟨ F ⊗ G ⟩ (x , y) = F x , G y
