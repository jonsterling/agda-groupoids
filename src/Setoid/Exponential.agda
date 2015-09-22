{-# OPTIONS --without-K #-}

module Setoid.Exponential where

open import Agda.Primitive
import Setoid.Base as S
open import Setoid.Exponential.Boot public
open import Setoid.Tensor.Boot as ∐
import Setoid.Terminal as 𝟙
import Setoid.Transfor as TFor
open import Type as T
  using (_,_)

infixr 2 _⇒₀ˢ_
infixr 2 _∘₀_
infixr 2 _∘₁_

_⇒₀ˢ_ : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t ℓ₀ᵒ ℓ₀ʰ)
  → (B : S.t ℓ₁ᵒ ℓ₁ʰ)
  → S.t _ _
S.obj (A ⇒₀ˢ B) =
  A ⇒₀ᵗ B
S.homᵗ (A ⇒₀ˢ B) =
  λ {(F , G) → F TFor.⇒₁ G}
S.idnᵗᵐ (A ⇒₀ˢ B) =
  TFor.idnᵗᵐ _
S.cmpᵗᵐ (A ⇒₀ˢ B) =
  TFor.cmpᵗᵐ
S.invᵗᵐ (A ⇒₀ˢ B) =
  TFor.invᵗᵐ

idn
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → 𝟙.s ⇒₀ᵗ (A ⇒₀ˢ A)
_$₀_ idn = idnᵗᵐ
_$₁_ idn = TFor.idnᵗᵐ _

cmp
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ˢ C) ∐.⊗ (A ⇒₀ˢ B) ⇒₀ᵗ (A ⇒₀ˢ C)
_$₀_ cmp = cmpᵗᵐ
_$₁_ cmp = TFor.cmpᵗᵐ-h₁

_∘₀_
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → (G : B ⇒₀ᵗ C)
  → (F : A ⇒₀ᵗ B)
  → (A ⇒₀ᵗ C)
G ∘₀ F = G ∘ᵗᵐ F

_∘₁_
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A ⇒₀ᵗ B}
  → {H K : B ⇒₀ᵗ C}
  → (β : H TFor.⇒₁ K)
  → (α : F TFor.⇒₁ G)
  → (H ∘ᵗᵐ F) TFor.⇒₁ (K ∘ᵗᵐ G)
β ∘₁ α = cmp $₁ (β , α)

! : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → S.obj A → (B ⇒₀ᵗ A)
_$₀_ (! a) = T.Π.! a
_$₁_ (! {A = A} _) = T.Π.! (S.idnᵗᵐ A T.𝟙.*)
