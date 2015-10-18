{-# OPTIONS --without-K #-}

module Ambient.Setoid.Base where

open import Agda.Primitive
open import Common public
open import Type

record 𝔊₁ d ..(ℓᵒ ℓʰ : _) : Set (lsuc (ℓᵒ ⊔ ℓʰ)) where
  no-eta-equality
  field
    cell₀
      : Set ℓᵒ
    cell₁
      : cell₀ ×₀ cell₀ → Set ℓʰ
    idn
      : ∀ {a}
      → 𝟙₀ {lzero} ⇒₀,₀ cell₁ (a , a)
    cmp
      : ∀ {a b c}
      → cell₁ (b , c) ×₀ cell₁ (a , b) ⇒₀,₀ cell₁ (a , c)
    {inv}
      : ∀ {a b}
      → Dir.el d 𝟙₀ (cell₁ (a , b) ⇒₀,₀ cell₁ (b , a))
open 𝔊₁ public

T↑S : ∀ {d} ..{ℓᵒ}
  → (A : 𝔊₀ ℓᵒ )
  → 𝔊₁ d _ lzero
cell₀ (T↑S A) =
  A
cell₁ (T↑S A) _ =
  𝟙₀
idn (T↑S A) =
  _
cmp (T↑S A) =
  _
inv (T↑S {Dir.≤} A) =
  _
inv (T↑S {Dir.≈} A) =
  _

S↓T : ∀ {d} ..{ℓᵒ ℓʰ}
  → (A : 𝔊₁ d ℓᵒ ℓʰ)
  → 𝔊₀ _
S↓T = cell₀
