{-# OPTIONS --without-K #-}

module Ambient.Type.Map where

open import Agda.Primitive
open import Ambient.Type.Base
open import Ambient.Type.Discrete as ≡
  using (_≡₀_)
open import Ambient.Type.Map.Boot public
open import Ambient.Type.Product.Boot
open import Ambient.Type.Terminal

infixr 0 _⇒₀,₁_

record _⇒₀,₁_ ..{ℓ₀ᵒ ℓ₁ᵒ}
  {A : 𝔊₀ ℓ₀ᵒ}
  {B : 𝔊₀ ℓ₁ᵒ}
  (F G : A ⇒₀,₀ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ᵒ) where
  no-eta-equality
  infixl 1 _·₀,₁_
  field
    _·₀,₁_
      : ∀ x
      → F x ≡₀ G x
open _⇒₀,₁_ public

idn₁
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ}
  → {A : 𝔊₀ ℓ₀ᵒ} {B : 𝔊₀ ℓ₁ᵒ}
  → (F : A ⇒₀,₀ B)
  → 𝟙₀ {lzero} ⇒₀,₀ (F ⇒₀,₁ F)
_·₀,₁_ (idn₁ F *) a = ≡.idn *

cmp₁
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ}
  → {A : 𝔊₀ ℓ₀ᵒ} {B : 𝔊₀ ℓ₁ᵒ}
  → {F G H : A ⇒₀,₀ B}
  → (G ⇒₀,₁ H) ×₀ (F ⇒₀,₁ G)
  → F ⇒₀,₁ H
_·₀,₁_ (cmp₁ (β , α)) a = ≡.cmp (β ·₀,₁ a , α ·₀,₁ a)

inv₁
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ}
  → {A : 𝔊₀ ℓ₀ᵒ} {B : 𝔊₀ ℓ₁ᵒ}
  → {F G : A ⇒₀,₀ B}
  → (F ⇒₀,₁ G) ⇒₀,₀ (G ⇒₀,₁ F)
_·₀,₁_ (inv₁ α) a = ≡.inv (α ·₀,₁ a)

cmp₁-₀w₁
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : 𝔊₀ ℓ₀ᵒ} {B : 𝔊₀ ℓ₁ᵒ} {C : 𝔊₀ ℓ₂ᵒ}
  → {F G : A ⇒₀,₀ B}
  → (Hα : (B ⇒₀,₀ C) ×₀ (F ⇒₀,₁ G))
  → (π⁰₀ Hα ∘₀ F) ⇒₀,₁ (π⁰₀ Hα ∘₀ G)
_·₀,₁_ (cmp₁-₀w₁ (H , α)) a = H ≡.$₁ (α ·₀,₁ a)

cmp₁-₁w₀_
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : 𝔊₀ ℓ₀ᵒ} {B : 𝔊₀ ℓ₁ᵒ} {C : 𝔊₀ ℓ₂ᵒ}
  → {G H : B ⇒₀,₀ C}
  → (βF : (G ⇒₀,₁ H) ×₀ (A ⇒₀,₀ B))
  → (G ∘₀ π¹₀ βF) ⇒₀,₁ (H ∘₀ π¹₀ βF)
_·₀,₁_ (cmp₁-₁w₀ (β , F)) a = β ·₀,₁ (F ·₀,₀ a)

cmp₁-h₀
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : 𝔊₀ ℓ₀ᵒ} {B : 𝔊₀ ℓ₁ᵒ} {C : 𝔊₀ ℓ₂ᵒ}
  → {F G : A ⇒₀,₀ B}
  → {H K : B ⇒₀,₀ C}
  → (βα : (H ⇒₀,₁ K) ×₀ (F ⇒₀,₁ G))
  → (H ∘₀ F) ⇒₀,₁ (K ∘₀ G)
_·₀,₁_ (cmp₁-h₀ {F = F}{K = K} (β , α)) a =
  ≡.cmp (K ≡.$₁ (α ·₀,₁ a) , β ·₀,₁ (F ·₀,₀ a))

cmp₁-h₁
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : 𝔊₀ ℓ₀ᵒ} {B : 𝔊₀ ℓ₁ᵒ} {C : 𝔊₀ ℓ₂ᵒ}
  → {F G : A ⇒₀,₀ B}
  → {H K : B ⇒₀,₀ C}
  → (βα : (H ⇒₀,₁ K) ×₀ (F ⇒₀,₁ G))
  → (H ∘₀ F) ⇒₀,₁ (K ∘₀ G)
_·₀,₁_ (cmp₁-h₁ {F = F}{G = G}{H = H} (β , α)) a =
  ≡.cmp (β ·₀,₁ (G ·₀,₀ a) , H ≡.$₁ (α ·₀,₁ a))
