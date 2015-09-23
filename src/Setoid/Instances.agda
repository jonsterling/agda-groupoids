{-# OPTIONS --without-K #-}

import Common

module Setoid.Instances where

open import Agda.Primitive
import Setoid.Base as S
import Setoid.Exponential as Π
import Setoid.Reasoning
import Setoid.Transfor as TFor

open S.t ⦃ … ⦄ public
open Π._⇒₀ᵗ_ ⦃ … ⦄ public
open TFor._⇒₁_ ⦃ … ⦄ public
open Setoid.Reasoning ⦃ … ⦄ public
