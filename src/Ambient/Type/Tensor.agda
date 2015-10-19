{-# OPTIONS --without-K #-}

module Ambient.Type.Tensor where

open import Agda.Primitive
import Ambient.Type.Map.Boot as Map
open import Ambient.Type.Tensor.Boot public

⟨_,_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {X : Set ℓ₀} {A : Set ℓ₁} {B : Set ℓ₂}
  → (F : X Map.⇒₀ A)
  → (G : X Map.⇒₀ B)
  → (X Map.⇒₀ A ⊗ B)
⟨ F , G ⟩ x = F x , G x

⟨_⊗_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
  → {X₀ : Set ℓ₀} {X₁ : Set ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃}
  → (F : X₀ Map.⇒₀ A)
  → (G : X₁ Map.⇒₀ B)
  → (X₀ ⊗ X₁ Map.⇒₀ A ⊗ B)
⟨ F ⊗ G ⟩ (x , y) = F x , G y

ap-lhs
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → A ⊗ B Map.⇒₀ C
  → (a : A)
  → B Map.⇒₀ C
ap-lhs F a = λ b → F (a , b)

ap-rhs
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (F : A ⊗ B Map.⇒₀ C)
  → (b : B)
  → A Map.⇒₀ C
ap-rhs F b = λ a → F (a , b)

curry
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (F : A ⊗ B Map.⇒₀ C)
  → A Map.⇒₀ B Map.⇒₀ C
curry F = λ a → ap-lhs F a

uncurry
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (F : A Map.⇒₀ B Map.⇒₀ C)
  → A ⊗ B Map.⇒₀ C
uncurry F (x , y) = F x y
