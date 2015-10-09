{-# OPTIONS --without-K #-}

module Category where

open import Agda.Primitive
import Groupoid.Core.Base
open import Common public

t : ∀ ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) → Set (lsuc (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ))
t = Groupoid.Core.Base.t Dir.≤

import Groupoid.Closed
import Groupoid.Core.Discrete
import Groupoid.Core.Hom
import Groupoid.Core.Homotopy
import Groupoid.Core.Initial
import Groupoid.Core.Op
import Groupoid.Core.Tensor
import Groupoid.Core.Terminal
import Groupoid.Monoidal

module Discrete = Groupoid.Core.Discrete
module Π where
  open import Groupoid.Core.Hom public
  open import Groupoid.Core.Hom.Boot public
module TFor = Groupoid.Core.Homotopy
module 𝟘 = Groupoid.Core.Initial
module Op = Groupoid.Core.Op
module ∐ where
  open import Groupoid.Core.Tensor public
  open import Groupoid.Core.Tensor.Boot public
module 𝟙 = Groupoid.Core.Terminal
