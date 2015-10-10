{-# OPTIONS --without-K #-}

module Category.Instances.SETOID where

open import Agda.Primitive
import Category as C
open import Common
import Setoid as S
open import Type as T
  using (_,_)

c : ..(ℓᵒ ℓʰ : _) → C.t _ _ _
C.obj (c ℓᵒ ℓʰ) =
  S.t Dir.≈ ℓᵒ ℓʰ
C.homˢ (c ℓᵒ ℓʰ) =
  λ {(a , b) → a S.Π.⇒₀ˢ b}
C.idnˢᵐ (c ℓᵒ ℓʰ) =
  S.Π.idn
C.cmpˢᵐ (c ℓᵒ ℓʰ) =
  S.Π.cmp
S.TFor.com₁ (C.idn-lhs (c ℓᵒ ℓʰ) {b = B} f) =
  S.idnᵗᵐ B _
S.TFor.com₁ (C.idn-rhs (c ℓᵒ ℓʰ) {b = B} f) =
  S.idnᵗᵐ B _
S.TFor.com₁ (C.cmp-ass (c ℓᵒ ℓʰ) {d = D} f g h) =
  S.idnᵗᵐ D _
C.invˢᵐ (c ℓᵒ ℓʰ) =
  _
C.inv-lhs (c ℓᵒ ℓʰ) =
  _
C.inv-rhs (c ℓᵒ ℓʰ) =
  _
