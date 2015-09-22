{-# OPTIONS --without-K #-}

module Setoid.Path where

import Setoid.Base as S
open import Type as T
  using (_,_)

s : ∀ {d} ..{ℓᵒ}
  → (A : T.t ℓᵒ)
  → S.t d ℓᵒ ℓᵒ
S.obj (s A) = A
S.homᵗ (s A) = λ {(a , b) → T.Path.t a b}
S.idnᵗᵐ (s A) = T.Path.idn
S.cmpᵗᵐ (s A) = T.Path.cmp
S.invᵗᵐ (s {S.Dir.≤} A) = _
S.invᵗᵐ (s {S.Dir.≈} A) = T.Path.inv
