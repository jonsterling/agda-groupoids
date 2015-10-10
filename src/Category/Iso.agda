{-# OPTIONS --without-K #-}

module Category.Iso where

open import Agda.Primitive
open import Common
import Groupoid as G
module C where
  open import Category public
  module ≅ where
    open import Groupoid.Iso {Dir.≤} public
import Category as C
import Setoid as S
open import Type as T
  using (_,_)

t : ∀ ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.t Dir.≤ ℓᵒ ℓˢᵒ ℓˢʰ}
  → _
t {A = A} = C.≅.t {A = A}
