{-# OPTIONS --without-K #-}

module Setoid.Base where

open import Agda.Primitive
open import Type as T
  using (_,_)

record t ..(ℓᵒ ℓʰ : _) : Set (lsuc (ℓᵒ ⊔ ℓʰ)) where
  no-eta-equality
  field
    obj : Set ℓᵒ
    homᵗ : obj T.∐.⊗ obj → Set ℓʰ
    idnᵗᵐ : ∀ {a} → T.𝟙.t T.Π.⇒₀ homᵗ (a , a)
    cmpᵗᵐ : ∀ {a b c} → homᵗ (b , c) T.∐.⊗ homᵗ (a , b) T.Π.⇒₀ homᵗ (a , c)
    invᵗᵐ : ∀ {a b} → homᵗ (a , b) T.Π.⇒₀ homᵗ (b , a)
open t public
