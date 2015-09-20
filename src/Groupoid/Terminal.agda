{-# OPTIONS --sized-types --without-K #-}

module Groupoid.Terminal where

open import Agda.Primitive
import Groupoid.Base as G
import Setoid as S
import Type as T

g : G.t lzero lzero lzero
G.obj g = T.𝟙.t
G.homˢ g = T.Π.! S.𝟙.s
G.idnˢᵐ g = S.Π.! T.𝟙.*
G.cmpˢᵐ g = S.Π.! T.𝟙.*
G.invˢᵐ g = S.Π.! T.𝟙.*
G.idn-lhs g = _
G.idn-rhs g = _
G.cmp-ass g = _
G.inv-lhs g = _
G.inv-rhs g = _
