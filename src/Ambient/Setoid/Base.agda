{-# OPTIONS --without-K #-}

module Ambient.Setoid.Base where

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
      : obj T.Ten.⊗ obj → Set ℓʰ
    idnᵗ
      : ∀ {a}
      → T.𝟙.t⁰ T.Map.⇒₀ homᵗ (a , a)
    cmpᵗ
      : ∀ {a b c}
      → homᵗ (b , c) T.Ten.⊗ homᵗ (a , b) T.Map.⇒₀ homᵗ (a , c)
    {invᵗ}
      : ∀ {a b}
      → Dir.el d T.𝟙.t (homᵗ (a , b) T.Map.⇒₀ homᵗ (b , a))
open t public

T↑S : ∀ {d} ..{ℓᵒ}
  → (A : T.t ℓᵒ )
  → t d _ lzero
obj (T↑S A) =
  A
homᵗ (T↑S A) _ =
  T.𝟙.t
idnᵗ (T↑S A) =
  _
cmpᵗ (T↑S A) =
  _
invᵗ (T↑S {Dir.≤} A) =
  _
invᵗ (T↑S {Dir.≈} A) =
  _

S↓T : ∀ {d} ..{ℓᵒ ℓʰ}
  → (A : t d ℓᵒ ℓʰ)
  → T.t _
S↓T = obj
