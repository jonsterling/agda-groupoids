{-# OPTIONS --without-K #-}

module Category.Iso where

open import Agda.Primitive
import Category as C
import Groupoid as G
import Setoid as S
open import Type as T
  using (_,_)
import Groupoid.Iso as GI

t : ∀ ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.𝔊₂,₀ G.Dir.≤ ℓᵒ ℓˢᵒ ℓˢʰ}
  → _
t {A = A} = GI.t {A = A}

s : ∀ ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.𝔊₂,₀ G.Dir.≤ ℓᵒ ℓˢᵒ ℓˢʰ}
  → _
s {A = A} = GI.s {A = A}

c : ∀ ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → (A : G.𝔊₂,₀ G.Dir.≤ ℓᵒ ℓˢᵒ ℓˢʰ)
  → _
c A = GI.g G.Dir.≤ A
