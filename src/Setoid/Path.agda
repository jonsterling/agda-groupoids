{-# OPTIONS --without-K #-}

module Setoid.Path where

import Setoid.Base as S
open import Type as T
  using (_,_)

s : ∀ ..{ℓᵒ} (A : T.t ℓᵒ) → S.t ℓᵒ ℓᵒ
S.obj (s A) = A
S.homᵗ (s A) = λ {(a , b) → T.Path.t a b}
S.idnᵗᵐ (s A) = T.Path.idn
S.cmpᵗᵐ (s A) = T.Path.cmp
S.invᵗᵐ (s A) = T.Path.inv
