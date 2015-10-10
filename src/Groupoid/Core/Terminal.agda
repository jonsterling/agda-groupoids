{-# OPTIONS --without-K #-}

module Groupoid.Core.Terminal where

open import Agda.Primitive
import Groupoid.Core.Base as G
import Setoid as S
import Type as T

g : ∀ {d} → G.t d lzero lzero lzero
G.obj g = T.𝟙.t
G.homˢ g = T.Π.! S.𝟙.s
G.idnˢ g = S.Π.!ˢ T.𝟙.*
G.cmpˢ g = S.Π.!ˢ T.𝟙.*
G.invˢ (g {G.Dir.≤}) = _
G.invˢ (g {G.Dir.≈}) = S.Π.!ˢ T.𝟙.*
G.idn-lhs g = _
G.idn-rhs g = _
G.cmp-ass g = _
G.inv-lhs (g {G.Dir.≤}) = _
G.inv-lhs (g {G.Dir.≈}) = _
G.inv-rhs (g {G.Dir.≤}) = _
G.inv-rhs (g {G.Dir.≈}) = _
