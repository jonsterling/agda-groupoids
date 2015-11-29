{-# OPTIONS --without-K #-}

module Ambient.Setoid.Trivial where

open import Agda.Primitive
import Ambient.Setoid.Base as S
open import Type as T
  using (_,_)

s : ∀ {d} ..{ℓᵒ ℓʰ}
  → (A : T.t ℓᵒ)
  → S.t d ℓᵒ ℓʰ
S.obj (s A) =
  A
S.homᵗ (s A) _ =
  T.𝟙.t
S.idnᵗ (s A) =
  _
S.cmpᵗ (s A) =
  _
S.invᵗ (s {S.Dir.≤} A) =
  _
S.invᵗ (s {S.Dir.≈} A) =
  _
