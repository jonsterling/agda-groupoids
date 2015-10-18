{-# OPTIONS --without-K #-}

module Ambient.Setoid.Discrete where

open import Agda.Primitive
import Ambient.Setoid.Base as S
open import Type as T

s
  : ∀ {d} ..{ℓᵒ}
  → (A : 𝔊₀ ℓᵒ)
  → S.𝔊₁ d _ _
S.cell₀ (s A) =
  A
S.cell₁ (s A) =
  λ {(a , b) → a T.≡₀ b}
S.idn (s A) =
  ≡₀.idn
S.cmp (s A) =
  ≡₀.cmp
S.inv (s {S.Dir.≤} A) =
  _
S.inv (s {S.Dir.≈} A) =
  ≡₀.inv
