{-# OPTIONS --without-K #-}

module Groupoid.Tensor where

open import Agda.Primitive
import Groupoid.Base as G
open import Groupoid.Exponential as Π
import Groupoid.Homotopy as TFor
open import Groupoid.Tensor.Boot public
import Setoid as S
open import Type as T
  using (_,_)

π₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A ⊗ B) Π.⇒₀ᵗ A
_$₀_ π₀ =
  T.∐.π₀
-$₁ˢᵐ- π₀ =
  S.∐.π₀
idn (π₀ {A = A}) =
  λ {a} → S.idnᵗᵐ (G.homˢ A (T.∐.π₀ a , T.∐.π₀ a)) _
cmp (π₀ {A = A}) =
  λ {a}{_}{c} _ _ → S.idnᵗᵐ (G.homˢ A (T.∐.π₀ a , T.∐.π₀ c)) _

π₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A ⊗ B) Π.⇒₀ᵗ B
_$₀_ π₁ =
  T.∐.π₁
-$₁ˢᵐ- π₁ =
  S.∐.π₁
idn (π₁ {B = B}) =
  λ {a} → S.idnᵗᵐ (G.homˢ B (T.∐.π₁ a , T.∐.π₁ a)) _
cmp (π₁ {B = B}) =
  λ {a}{_}{c} _ _ → S.idnᵗᵐ (G.homˢ B (T.∐.π₁ a , T.∐.π₁ c)) _
