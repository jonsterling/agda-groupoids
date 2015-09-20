{-# OPTIONS --sized-types --without-K #-}

module Groupoid.Initial where

open import Agda.Primitive
import Groupoid.Base as G
import Setoid as S
import Type as T

g : G.t lzero lzero lzero
G.obj g = T.𝟘.t
G.homˢ g = λ { (() T., _) }
G.idnˢᵐ g = λ {}
G.cmpˢᵐ g = λ {}
G.invˢᵐ g = λ {}
G.idn-lhs g = λ {}
G.idn-rhs g = λ {}
G.cmp-ass g = λ {}
G.inv-lhs g = λ {}
G.inv-rhs g = λ {}
