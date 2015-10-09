{-# OPTIONS --without-K #-}

module Type.Core.Op where

import Type.Core.Base as T

t : ∀ ..{ℓᵒ} → T.t ℓᵒ → T.t ℓᵒ
t A = A
