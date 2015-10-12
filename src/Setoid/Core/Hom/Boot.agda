{-# OPTIONS --without-K #-}

module Setoid.Core.Hom.Boot where

open import Agda.Primitive
import Setoid.Core.Base as S
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
      : S.obj A T.Π.⇒₀ S.obj B
    ._$₁_
      : ∀ {a b}
      → S.homᵗ A (a , b) T.Π.⇒₀ S.homᵗ B (_$₀_ a , _$₀_ b)
open _⇒₀ᵗ_ public

idn₀ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → T.𝟙.t⁰ T.Π.⇒₀ (A ⇒₀ᵗ A)
_$₀_ (idn₀ᵗ T.𝟙.*) = T.Π.idn
_$₁_ (idn₀ᵗ T.𝟙.*) = T.Π.idn

cmp₀ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ᵗ C) T.∐.⊗ (A ⇒₀ᵗ B) T.Π.⇒₀ (A ⇒₀ᵗ C)
_$₀_ (cmp₀ᵗ (G , F)) = (G $₀_) T.Π.∘ (F $₀_)
_$₁_ (cmp₀ᵗ (G , F)) = (G $₁_) T.Π.∘ (F $₁_)

_∘₀ᵗ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ᵗ C) T.Π.⇒₀ (A ⇒₀ᵗ B) T.Π.⇒₀ (A ⇒₀ᵗ C)
_∘₀ᵗ_ G F = cmp₀ᵗ (G , F)
