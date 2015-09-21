{-# OPTIONS --without-K #-}

module Setoid.Tensor where

open import Agda.Primitive
import Setoid.Base as S
open import Setoid.Exponential as Π
open import Setoid.Tensor.Boot public
import Setoid.Transfor as TFor
import Type as T

π₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → (A ⊗ B) Π.⇒₀ᵗ A
_$₀_ π₀ = T.∐.π₀
_$₁_ π₀ = T.∐.π₀

π₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → (A ⊗ B) Π.⇒₀ᵗ B
_$₀_ π₁ = T.∐.π₁
_$₁_ π₁ = T.∐.π₁

⟨-,-⟩
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {X : S.t ℓ₀ᵒ ℓ₀ʰ} {A : S.t ℓ₁ᵒ ℓ₁ʰ} {B : S.t ℓ₂ᵒ ℓ₂ʰ}
  → ((X Π.⇒₀ˢ A) ⊗ (X Π.⇒₀ˢ B)) Π.⇒₀ᵗ (X Π.⇒₀ˢ A ⊗ B)
_$₀_ (_$₀_ ⟨-,-⟩ FG) = T.∐.⟨ T.∐.π₀ FG $₀_ , T.∐.π₁ FG $₀_ ⟩
_$₁_ (_$₀_ ⟨-,-⟩ FG) = T.∐.⟨ T.∐.π₀ FG $₁_ , T.∐.π₁ FG $₁_ ⟩
_$₁_ ⟨-,-⟩ = TFor.nat₁ T.Π.∘ (λ x → T.∐.⟨ TFor.com₁′ ⊗ TFor.com₁′ ⟩ x)

⟨-⊗-⟩
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ ℓ₃ᵒ ℓ₃ʰ}
  → {X₀ : S.t ℓ₀ᵒ ℓ₀ʰ} {X₁ : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₂ᵒ ℓ₂ʰ} {B : S.t ℓ₃ᵒ ℓ₃ʰ}
  → ((X₀ Π.⇒₀ˢ A) ⊗ (X₁ Π.⇒₀ˢ B)) Π.⇒₀ᵗ ((X₀ ⊗ X₁) Π.⇒₀ˢ (A ⊗ B))
_$₀_ (_$₀_ ⟨-⊗-⟩ FG) = T.∐.⟨ T.∐.π₀ FG $₀_ ⊗ T.∐.π₁ FG $₀_ ⟩
_$₁_ (_$₀_ ⟨-⊗-⟩ FG) = T.∐.⟨ T.∐.π₀ FG $₁_ ⊗ T.∐.π₁ FG $₁_ ⟩
_$₁_ ⟨-⊗-⟩ = TFor.nat₁ T.Π.∘ (λ x → T.∐.⟨ TFor.com₁′ ⊗ TFor.com₁′ ⟩ x)
