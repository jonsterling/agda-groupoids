{-# OPTIONS --without-K #-}

module Ambient.Setoid.Map.Boot where

open import Agda.Primitive
import Ambient.Setoid.Base as S
open import Type as T
  using (_,_)

infixr 1 _⇒₀ᵗ_
infixr 2 _∘₀ᵗ_

record _⇒₀ᵗ_
  {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  (A : S.t d ℓ₀ᵒ ℓ₀ʰ)
  (B : S.t d ℓ₁ᵒ ℓ₁ʰ)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ʰ) ⊔ (ℓ₁ᵒ ⊔ ℓ₁ʰ)) where
  no-eta-equality
  infixr 4 _$₀_
  infixr 4 _$₁_
  field
    _$₀_
      : S.obj A T.Map.⇒₀ S.obj B
    ._$₁_
      : ∀ {a b}
      → S.homᵗ A (a , b) T.Map.⇒₀ S.homᵗ B (_$₀_ a , _$₀_ b)
open _⇒₀ᵗ_ public

idn₀ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → T.𝟙.t⁰ T.Map.⇒₀ (A ⇒₀ᵗ A)
_$₀_ (idn₀ᵗ T.𝟙.*) = T.Map.idn
_$₁_ (idn₀ᵗ T.𝟙.*) = T.Map.idn

cmp₀ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ᵗ C) T.Ten.⊗ (A ⇒₀ᵗ B) T.Map.⇒₀ (A ⇒₀ᵗ C)
_$₀_ (cmp₀ᵗ (G , F)) = (G $₀_) T.Map.∘ (F $₀_)
_$₁_ (cmp₀ᵗ (G , F)) = (G $₁_) T.Map.∘ (F $₁_)

_∘₀ᵗ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ᵗ C) T.Map.⇒₀ (A ⇒₀ᵗ B) T.Map.⇒₀ (A ⇒₀ᵗ C)
_∘₀ᵗ_ G F = cmp₀ᵗ (G , F)
