{-# OPTIONS --without-K #-}

module Ambient.Type.Op where

import Ambient.Type.Base as T

t : ∀ ..{ℓᵒ} → T.t ℓᵒ → T.t ℓᵒ
t A = A
