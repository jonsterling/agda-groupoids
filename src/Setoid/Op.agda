{-# OPTIONS --sized-types --without-K #-}

module Setoid.Op where

import Setoid.Base as S
import Type as T

s : ∀ ..{ℓᵒ ℓʰ} → S.t ℓᵒ ℓʰ → S.t ℓᵒ ℓʰ
S.obj (s A) = T.Op.t (S.obj A)
S.homᵗ (s A) = S.homᵗ A T.Π.∘ T.∐.⟨ T.∐.π₁ , T.∐.π₀ ⟩
S.idnᵗᵐ (s A) = S.idnᵗᵐ A
S.cmpᵗᵐ (s A) = S.cmpᵗᵐ A T.Π.∘ T.∐.⟨ T.∐.π₁ , T.∐.π₀ ⟩
S.invᵗᵐ (s A) = S.invᵗᵐ A
