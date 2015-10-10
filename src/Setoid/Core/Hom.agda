{-# OPTIONS --without-K #-}

module Setoid.Core.Hom where

open import Agda.Primitive
import Setoid.Core.Base as S
open import Setoid.Core.Hom.Boot public
import Setoid.Core.Homotopy as TF
open import Setoid.Core.Tensor.Boot as ∐
import Setoid.Core.Terminal as 𝟙
open import Type as T
  using (_,_)

infixr 2 _⇒₀ˢ_
infixr 2 _∘₀_
infixr 2 _∘₁_

_⇒₀ˢ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t d ℓ₀ᵒ ℓ₀ʰ)
  → (B : S.t d ℓ₁ᵒ ℓ₁ʰ)
  → S.t d _ _
S.obj (A ⇒₀ˢ B) =
  A ⇒₀ᵗ B
S.homᵗ (A ⇒₀ˢ B) =
  λ {(F , G) → F TF.⇒₁ G}
S.idnᵗ (A ⇒₀ˢ B) =
  TF.idnᵗ _
S.cmpᵗ (A ⇒₀ˢ B) =
  TF.cmpᵗ
S.invᵗ (_⇒₀ˢ_ {S.Dir.≤} A B) =
  _
S.invᵗ (_⇒₀ˢ_ {S.Dir.≈} A B) =
  TF.invᵗ

idn
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → 𝟙.s ⇒₀ᵗ (A ⇒₀ˢ A)
_$₀_ idn = idnᵗ
_$₁_ idn = TF.idnᵗ _

cmp
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ˢ C) ∐.⊗ (A ⇒₀ˢ B) ⇒₀ᵗ (A ⇒₀ˢ C)
_$₀_ cmp = cmpᵗ
_$₁_ cmp = TF.cmpᵗ-h₁

_∘₀_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (G : B ⇒₀ᵗ C)
  → (F : A ⇒₀ᵗ B)
  → (A ⇒₀ᵗ C)
G ∘₀ F = G ∘ᵗ F

_∘₁_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A ⇒₀ᵗ B}
  → {H K : B ⇒₀ᵗ C}
  → (β : H TF.⇒₁ K)
  → (α : F TF.⇒₁ G)
  → (H ∘ᵗ F) TF.⇒₁ (K ∘ᵗ G)
β ∘₁ α = cmp $₁ (β , α)

! : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → S.obj A → (B ⇒₀ᵗ A)
_$₀_ (! a) = T.Π.! a
_$₁_ (! {A = A} _) = T.Π.! (S.idnᵗ A T.𝟙.*)
