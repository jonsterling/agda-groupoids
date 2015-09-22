{-# OPTIONS --without-K #-}

module Setoid.Base where

open import Agda.Primitive
open import Common public
open import Type as T
  using (_,_)

record t d ..(ℓᵒ ℓʰ : _) : Set (lsuc (ℓᵒ ⊔ ℓʰ)) where
  no-eta-equality
  field
    obj
      : Set ℓᵒ
    homᵗ
      : obj T.∐.⊗ obj → Set ℓʰ
    idnᵗᵐ
      : ∀ {a}
      → T.𝟙.t⁰ T.Π.⇒₀ homᵗ (a , a)
    cmpᵗᵐ
      : ∀ {a b c}
      → homᵗ (b , c) T.∐.⊗ homᵗ (a , b) T.Π.⇒₀ homᵗ (a , c)
    {invᵗᵐ}
      : ∀ {a b}
      → Dir.el d T.𝟙.t (homᵗ (a , b) T.Π.⇒₀ homᵗ (b , a))
open t public
