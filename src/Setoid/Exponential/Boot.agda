{-# OPTIONS --without-K #-}

module Setoid.Exponential.Boot where

open import Agda.Primitive
import Setoid.Base as S
open import Type as T
  using (_,_)

infixr 1 _⇒₀ᵗ_
infixr 2 _∘ᵗᵐ_

record _⇒₀ᵗ_
  {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  (A : S.t d ℓ₀ᵒ ℓ₀ʰ)
  (B : S.t d ℓ₁ᵒ ℓ₁ʰ)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ʰ) ⊔ (ℓ₁ᵒ ⊔ ℓ₁ʰ)) where
  no-eta-equality
  infixr 2 _$₀_
  infixr 2 _$₁_
  field
    _$₀_ : S.obj A T.Π.⇒₀ S.obj B
    _$₁_ : ∀ {a b} → S.homᵗ A (a , b) T.Π.⇒₀ S.homᵗ B (_$₀_ a , _$₀_ b)
open _⇒₀ᵗ_ public

idnᵗᵐ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → T.𝟙.t⁰ T.Π.⇒₀ (A ⇒₀ᵗ A)
_$₀_ (idnᵗᵐ T.𝟙.*) = T.Π.idn
_$₁_ (idnᵗᵐ T.𝟙.*) = T.Π.idn

cmpᵗᵐ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ᵗ C) T.∐.⊗ (A ⇒₀ᵗ B) T.Π.⇒₀ (A ⇒₀ᵗ C)
_$₀_ (cmpᵗᵐ (G , F)) = (G $₀_) T.Π.∘ (F $₀_)
_$₁_ (cmpᵗᵐ (G , F)) = (G $₁_) T.Π.∘ (F $₁_)

_∘ᵗᵐ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ᵗ C) T.Π.⇒₀ (A ⇒₀ᵗ B) T.Π.⇒₀ (A ⇒₀ᵗ C)
_∘ᵗᵐ_ G F = cmpᵗᵐ (G , F)
