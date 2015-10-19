{-# OPTIONS --without-K #-}

module Ambient.Type.Map where

open import Agda.Primitive
import Ambient.Type.Base as T
import Ambient.Type.Discrete as ≡
  renaming (t to _t_)
open import Ambient.Type.Map.Boot public
open import Ambient.Type.Tensor.Boot as Ten
  using (_,_)
import Ambient.Type.Terminal as 𝟙

infixr 0 _⇒₁_

record _⇒₁_ ..{ℓ₀ᵒ ℓ₁ᵒ}
  {A : T.t ℓ₀ᵒ}
  {B : T.t ℓ₁ᵒ}
  (F G : A ⇒₀ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ᵒ) where
  no-eta-equality
  field
    com₁
      : ∀ {x}
      → F x ≡.t G x
open _⇒₁_ public

idnᵗᵐ
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → (F : A ⇒₀ B)
  → 𝟙.t ⇒₀ (F ⇒₁ F)
com₁ (idnᵗᵐ F x) = ≡.idn x

cmpᵗᵐ
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → {F G H : A ⇒₀ B}
  → (G ⇒₁ H) Ten.⊗ (F ⇒₁ G)
  → F ⇒₁ H
com₁ (cmpᵗᵐ (β , α)) = ≡.cmp (com₁ β , com₁ α)

invᵗᵐ
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → {F G : A ⇒₀ B}
  → (F ⇒₁ G) ⇒₀ (G ⇒₁ F)
com₁ (invᵗᵐ α) = ≡.inv (com₁ α)

cmpᵗᵐ-w₀
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A ⇒₀ B}
  → (Hα : (B ⇒₀ C) Ten.⊗ (F ⇒₁ G))
  → (Ten.π₀ Hα ∘ F) ⇒₁ (Ten.π₀ Hα ∘ G)
com₁ (cmpᵗᵐ-w₀ (H , α)) = H ≡.$₁ com₁ α

cmpᵗᵐ-w₁_
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {G H : B ⇒₀ C}
  → (βF : (G ⇒₁ H) Ten.⊗ (A ⇒₀ B))
  → (G ∘ Ten.π₁ βF) ⇒₁ (H ∘ Ten.π₁ βF)
com₁ (cmpᵗᵐ-w₁ (β , F)) = com₁ β

cmpᵗᵐ-h₀
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A ⇒₀ B}
  → {H K : B ⇒₀ C}
  → (βα : (H ⇒₁ K) Ten.⊗ (F ⇒₁ G))
  → (H ∘ F) ⇒₁ (K ∘ G)
com₁ (cmpᵗᵐ-h₀ {K = K} (β , α)) = ≡.cmp (K ≡.$₁ com₁ α , com₁ β)

cmpᵗᵐ-h₁
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A ⇒₀ B}
  → {H K : B ⇒₀ C}
  → (βα : (H ⇒₁ K) Ten.⊗ (F ⇒₁ G))
  → (H ∘ F) ⇒₁ (K ∘ G)
com₁ (cmpᵗᵐ-h₁ {H = H} (β , α)) = ≡.cmp (com₁ β , H ≡.$₁ com₁ α)
