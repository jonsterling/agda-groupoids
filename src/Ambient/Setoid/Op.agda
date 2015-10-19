{-# OPTIONS --without-K #-}

module Ambient.Setoid.Op where

open import Agda.Primitive
import Ambient.Setoid.Base as S
import Type as T

s : ∀ {d} ..{ℓᵒ ℓʰ}
  → S.t d ℓᵒ ℓʰ
  → S.t d ℓᵒ ℓʰ
S.obj (s A) =
  T.Op.t (S.obj A)
S.homᵗ (s A) =
  S.homᵗ A T.Map.∘ T.Ten.⟨ T.Ten.π₁ , T.Ten.π₀ ⟩
S.idnᵗ (s A) =
  S.idnᵗ A
S.cmpᵗ (s A) =
  S.cmpᵗ A T.Map.∘ T.Ten.⟨ T.Ten.π₁ , T.Ten.π₀ ⟩
S.invᵗ (s A) =
  S.invᵗ A
