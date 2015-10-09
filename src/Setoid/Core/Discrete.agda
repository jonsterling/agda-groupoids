{-# OPTIONS --without-K #-}

module Setoid.Core.Discrete where

open import Agda.Primitive
import Setoid.Core.Base as S
open import Type as T
  using (_,_)

s : ∀ {d} ..{ℓᵒ}
  → (A : T.t ℓᵒ)
  → S.t d _ _
S.obj (s A) =
  A
S.homᵗ (s A) =
  λ {(a , b) → a T.≡.t b}
S.idnᵗᵐ (s A) =
  T.≡.idn
S.cmpᵗᵐ (s A) =
  T.≡.cmp
S.invᵗᵐ (s {S.Dir.≤} A) =
  _
S.invᵗᵐ (s {S.Dir.≈} A) =
  T.≡.inv
