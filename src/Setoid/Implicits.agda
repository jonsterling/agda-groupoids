{-# OPTIONS --without-K #-}

import Common

module Setoid.Implicits where

open import Agda.Primitive
import Setoid.Core.Base as S
import Setoid.Core.Hom as Π
import Setoid.Core.Homotopy as TF
import Setoid.Reasoning

open S.t ⦃ … ⦄ public
open Π._⇒₀ᵗ_ ⦃ … ⦄ public
open TF._⇒₁_ ⦃ … ⦄ public
open Setoid.Reasoning ⦃ … ⦄ public
