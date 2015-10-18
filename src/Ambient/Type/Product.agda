{-# OPTIONS --without-K #-}

module Ambient.Type.Product where

open import Agda.Primitive
open import Ambient.Type.Map.Boot
open import Ambient.Type.Product.Boot public

⟨_,₀_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {X : Set ℓ₀} {A : Set ℓ₁} {B : Set ℓ₂}
  → (F : X ⇒₀,₀ A)
  → (G : X ⇒₀,₀ B)
  → (X ⇒₀,₀ A ×₀ B)
⟨ F ,₀ G ⟩ x = F x , G x

⟨_×₀_⟩
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂ ℓ₃}
  → {X₀ : Set ℓ₀} {X₁ : Set ℓ₁} {A : Set ℓ₂} {B : Set ℓ₃}
  → (F : X₀ ⇒₀,₀ A)
  → (G : X₁ ⇒₀,₀ B)
  → (X₀ ×₀ X₁ ⇒₀,₀ A ×₀ B)
⟨ F ×₀ G ⟩ (x , y) = F x , G y

-- curry
--   : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
--   → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
--   → (F : A ×₀ B Map.⇒₀,₀ C)
--   → A Map.⇒₀,₀ B Map.⇒₀,₀ C
-- curry F = λ a → ap-lhs F a

-- uncurry
--   : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
--   → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
--   → (F : A Map.⇒₀,₀ B Map.⇒₀,₀ C)
--   → A ×₀ B Map.⇒₀,₀ C
-- uncurry F (x , y) = F x y

-- ap-lhs
--   : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
--   → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
--   → A ×₀ B Map.⇒₀,₀ C
--   → ((a : A) → B Map.⇒₀,₀ C)
-- ap-lhs F a = λ b → F (a , b)

-- ap-rhs
--   : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
--   → {A : Set ℓ₀} {B : Set ℓ₁} {C : Set ℓ₂}
--   → (F : A ×₀ B Map.⇒₀,₀ C)
--   → ((b : B) → A Map.⇒₀,₀ C)
-- ap-rhs F b = λ a → F (a , b)
