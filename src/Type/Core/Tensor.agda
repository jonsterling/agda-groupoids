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

ap-lhs
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → A ⊗ B Π.⇒₀ C
  → (a : A)
  → B Π.⇒₀ C
ap-lhs F a = λ b → F (a , b)

ap-rhs
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (F : A ⊗ B Π.⇒₀ C)
  → (b : B)
  → A Π.⇒₀ C
ap-rhs F b = λ a → F (a , b)

curry
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (F : A ⊗ B Π.⇒₀ C)
  → A Π.⇒₀ B Π.⇒₀ C
curry F = λ a → ap-lhs F a

uncurry
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
  → (F : A Π.⇒₀ B Π.⇒₀ C)
  → A ⊗ B Π.⇒₀ C
uncurry F (x , y) = F x y
