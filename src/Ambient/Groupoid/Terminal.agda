{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Terminal where

open import Agda.Primitive
import Ambient.Groupoid.Base as G
import Setoid as S
open import Type as T

g : ∀ {d} → G.𝔊₂,₀ d lzero lzero lzero
G.obj g = 𝟙₀
G.homˢ g = ⇒₀.elm₀ S.𝟙.s
G.idnˢ g = S.Map.!ˢ *
G.cmpˢ g = S.Map.!ˢ *
G.invˢ (g {G.Dir.≤}) = _
G.invˢ (g {G.Dir.≈}) = S.Map.!ˢ *
G.idn-lhs g = _
G.idn-rhs g = _
G.cmp-ass g = _
G.inv-lhs (g {G.Dir.≤}) = _
G.inv-lhs (g {G.Dir.≈}) = _
G.inv-rhs (g {G.Dir.≤}) = _
G.inv-rhs (g {G.Dir.≈}) = _
