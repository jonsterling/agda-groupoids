{-# OPTIONS --without-K #-}

module Setoid.Core.Op where

open import Agda.Primitive
import Setoid.Core.Base as S
import Type as T

s : ∀ {d} ..{ℓᵒ ℓʰ}
  → S.t d ℓᵒ ℓʰ
  → S.t d ℓᵒ ℓʰ
S.obj (s A) =
  T.Op.t (S.obj A)
S.homᵗ (s A) =
  S.homᵗ A T.Π.∘ T.∐.⟨ T.∐.π₁ , T.∐.π₀ ⟩
S.idnᵗ (s A) =
  S.idnᵗ A
S.cmpᵗ (s A) =
  S.cmpᵗ A T.Π.∘ T.∐.⟨ T.∐.π₁ , T.∐.π₀ ⟩
S.invᵗ (s A) =
  S.invᵗ A
