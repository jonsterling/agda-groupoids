{-# OPTIONS --without-K #-}

module Type.Core.Initial where

open import Agda.Primitive

data t ..{ℓ} : Set ℓ where

¡ : ∀ ..{ℓ} {A : Set ℓ} → t {lzero} → A
¡ ()

¬_ : ∀ ..{ℓ} → Set ℓ → Set ℓ
¬_ A = A → t {lzero}
