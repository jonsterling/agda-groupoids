{-# OPTIONS --without-K #-}

import Common

module Setoid.Instances where

open import Agda.Primitive
import Setoid.Core.Base as S
import Setoid.Core.Exponential as Π
import Setoid.Core.Homotopy as TFor
import Setoid.Reasoning

open S.t ⦃ … ⦄ public
open Π._⇒₀ᵗ_ ⦃ … ⦄ public
open TFor._⇒₁_ ⦃ … ⦄ public
open Setoid.Reasoning ⦃ … ⦄ public
