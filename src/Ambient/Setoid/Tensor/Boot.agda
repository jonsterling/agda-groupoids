{-# OPTIONS --without-K #-}

module Ambient.Setoid.Tensor.Boot where

open import Agda.Primitive
import Ambient.Setoid.Base as S
open import Type as T
  using (_,_)

infixr 3 _⊗_

_⊗_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t d ℓ₀ᵒ ℓ₀ʰ)
  → (B : S.t d ℓ₁ᵒ ℓ₁ʰ)
  → S.t d _ _
S.obj (A ⊗ B) =
  S.t.obj A T.Ten.⊗ S.t.obj B
S.homᵗ (A ⊗ B) =
  λ {((a₀ , b₀) , (a₁ , b₁)) →
    S.homᵗ A (a₀ , a₁) T.Ten.⊗ S.homᵗ B (b₀ , b₁)
  }
S.idnᵗ (A ⊗ B) =
  T.Ten.⟨ S.idnᵗ A , S.idnᵗ B ⟩
S.cmpᵗ (A ⊗ B) =
  T.Ten.⟨ S.cmpᵗ A T.Map.∘ T.Ten.⟨ T.Ten.π₀ ⊗ T.Ten.π₀ ⟩
        , S.cmpᵗ B T.Map.∘ T.Ten.⟨ T.Ten.π₁ ⊗ T.Ten.π₁ ⟩ ⟩
S.invᵗ (_⊗_ {S.Dir.≤} A B) =
  _
S.invᵗ (_⊗_ {S.Dir.≈} A B) =
  T.Ten.⟨ S.invᵗ A ⊗ S.invᵗ B ⟩
