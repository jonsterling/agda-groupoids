{-# OPTIONS --without-K #-}

open import Common
module Groupoid.Bifunctor {d : Dir.t} where

open import Agda.Primitive
import Groupoid as G
import Setoid as S
open import Type as T
  using (_,_)

module _ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ} where
  infixr 0 :⟨_,_⟩⇒₀ᵗ_
  infixr 2 :⟨_,_⟩⇒₀ᵍ_

  :⟨_,_⟩⇒₀ᵗ_
    : (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → (C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ)
    → Set _
  :⟨ A , B ⟩⇒₀ᵗ C = A G.∐.⊗ B G.Π.⇒₀ᵗ C

  :⟨_,_⟩⇒₀ᵍ_
    : (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → (C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ)
    → G.t _ _ _ _
  :⟨ A , B ⟩⇒₀ᵍ C = A G.∐.⊗ B G.Π.⇒₀ᵍ C
