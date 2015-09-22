{-# OPTIONS --without-K #-}

module Setoid.Discrete where

open import Agda.Primitive
import Setoid.Base as S
open import Type as T
  using (_,_)

s : ∀ {d} ..{ℓᵒ}
  → (A : T.t ℓᵒ)
  → S.t d ℓᵒ ℓᵒ
S.obj (s A) = A
S.homᵗ (s A) = λ {(a , b) → T.Discrete.t a b}
S.idnᵗᵐ (s A) = T.Discrete.idn
S.cmpᵗᵐ (s A) = T.Discrete.cmp
S.invᵗᵐ (s {S.Dir.≤} A) = _
S.invᵗᵐ (s {S.Dir.≈} A) = T.Discrete.inv
