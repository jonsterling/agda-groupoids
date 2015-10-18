{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Initial where

open import Agda.Primitive
import Ambient.Groupoid.Base as G
import Setoid as S
open import Type as T

g : ∀ {d} → G.𝔊₂,₀ d lzero lzero lzero
G.obj g = 𝟘₀
G.homˢ g = λ { (() T., _) }
G.idnˢ g = λ {}
G.cmpˢ g = λ {}
G.invˢ g = λ {}
G.idn-lhs g = λ {}
G.idn-rhs g = λ {}
G.cmp-ass g = λ {}
G.inv-lhs g = λ {}
G.inv-rhs g = λ {}
