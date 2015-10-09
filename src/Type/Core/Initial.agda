{-# OPTIONS --without-K #-}

module Type.Core.Initial where

open import Agda.Primitive

data t : Set where

¡ : ∀ ..{ℓ} {A : Set ℓ} → t → A
¡ ()

¬_ : ∀ ..{ℓ} → Set ℓ → Set ℓ
¬_ A = A → t
