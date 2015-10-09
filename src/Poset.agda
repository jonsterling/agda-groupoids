{-# OPTIONS --without-K #-}

module Poset where

open import Agda.Primitive
import Setoid.Core.Base
open import Common public

t : ∀ ..(ℓᵒ ℓʰ : _) → Set (lsuc (ℓᵒ ⊔ ℓʰ))
t = Setoid.Core.Base.t Dir.≤

import Setoid.Closed
import Setoid.Core.Discrete
import Setoid.Core.Hom
import Setoid.Core.Homotopy
import Setoid.Core.Initial
import Setoid.Core.Op
import Setoid.Core.Tensor
import Setoid.Core.Terminal
import Setoid.Monoidal

module Discrete = Setoid.Core.Discrete
module Π where
  open import Setoid.Core.Hom public
  open import Setoid.Core.Hom.Boot public
module TFor = Setoid.Core.Homotopy
module 𝟘 = Setoid.Core.Initial
module Op = Setoid.Core.Op
module ∐ where
  open import Setoid.Core.Tensor public
  open import Setoid.Core.Tensor.Boot public
module 𝟙 = Setoid.Core.Terminal
