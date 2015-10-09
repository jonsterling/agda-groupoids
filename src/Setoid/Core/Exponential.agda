{-# OPTIONS --without-K #-}

module Setoid.Core.Exponential where

open import Agda.Primitive
import Setoid.Core.Base as S
open import Setoid.Core.Exponential.Boot public
import Setoid.Core.Homotopy as TFor
open import Setoid.Core.Tensor.Boot as ∐
import Setoid.Core.Terminal as 𝟙
open import Type as T
  using (_,_)

infixr 2 _⇒₀ˢ_
infixr 2 _∘₀_
infixr 2 _∘₁_

_⇒₀ˢ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t d ℓ₀ᵒ ℓ₀ʰ)
  → (B : S.t d ℓ₁ᵒ ℓ₁ʰ)
  → S.t d _ _
S.obj (A ⇒₀ˢ B) =
  A ⇒₀ᵗ B
S.homᵗ (A ⇒₀ˢ B) =
  λ {(F , G) → F TFor.⇒₁ G}
S.idnᵗᵐ (A ⇒₀ˢ B) =
  TFor.idnᵗᵐ _
S.cmpᵗᵐ (A ⇒₀ˢ B) =
  TFor.cmpᵗᵐ
S.invᵗᵐ (_⇒₀ˢ_ {S.Dir.≤} A B) =
  _
S.invᵗᵐ (_⇒₀ˢ_ {S.Dir.≈} A B) =
  TFor.invᵗᵐ

idn
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → 𝟙.s ⇒₀ᵗ (A ⇒₀ˢ A)
_$₀_ idn = idnᵗᵐ
_$₁_ idn = TFor.idnᵗᵐ _

cmp
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ˢ C) ∐.⊗ (A ⇒₀ˢ B) ⇒₀ᵗ (A ⇒₀ˢ C)
_$₀_ cmp = cmpᵗᵐ
_$₁_ cmp = TFor.cmpᵗᵐ-h₁

_∘₀_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (G : B ⇒₀ᵗ C)
  → (F : A ⇒₀ᵗ B)
  → (A ⇒₀ᵗ C)
G ∘₀ F = G ∘ᵗᵐ F

_∘₁_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A ⇒₀ᵗ B}
  → {H K : B ⇒₀ᵗ C}
  → (β : H TFor.⇒₁ K)
  → (α : F TFor.⇒₁ G)
  → (H ∘ᵗᵐ F) TFor.⇒₁ (K ∘ᵗᵐ G)
β ∘₁ α = cmp $₁ (β , α)

! : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → S.obj A → (B ⇒₀ᵗ A)
_$₀_ (! a) = T.Π.! a
_$₁_ (! {A = A} _) = T.Π.! (S.idnᵗᵐ A T.𝟙.*)
