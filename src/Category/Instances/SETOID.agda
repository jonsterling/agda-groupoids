{-# OPTIONS --without-K #-}

module Category.Instances.SETOID where

open import Agda.Primitive
open import Common
import Category as C
import Setoid as S
open import Type as T
  using (_,_)

c : ..(ℓᵒ ℓʰ : _) → C.t _ _ _
C.obj (c ℓᵒ ℓʰ) =
  S.t Dir.≈ ℓᵒ ℓʰ
C.homˢ (c _ _) =
  λ {(a , b) → a S.Π.⇒₀ˢ b}
C.idnˢ (c _ _) =
  S.Π.idnˢ
C.cmpˢ (c _ _) =
  S.Π.cmpˢ
S.TF.com₁ (C.idn-lhs (c _ _) {b = B} _) =
  S.idnᵗ B _
S.TF.com₁ (C.idn-rhs (c _ _) {b = B} _) =
  S.idnᵗ B _
S.TF.com₁ (C.cmp-ass (c _ _) {d = D} _ _ _) =
  S.idnᵗ D _
C.invˢ (c _ _) =
  _
C.inv-lhs (c _ _) =
  _
C.inv-rhs (c _ _) =
  _
