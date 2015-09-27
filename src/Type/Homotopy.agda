{-# OPTIONS --without-K #-}

module Type.Homotopy where

open import Agda.Primitive
import Type.Base as T
import Type.Discrete as Discrete
  renaming (t to _≡_)
import Type.Exponential as Π
open import Type.Tensor as ∐
  using (_,_)
import Type.Terminal as 𝟙

infixr 0 _⇒₁_

record _⇒₁_ ..{ℓ₀ᵒ ℓ₁ᵒ}
  {A : T.t ℓ₀ᵒ}
  {B : T.t ℓ₁ᵒ}
  (F G : A Π.⇒₀ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ᵒ) where
  no-eta-equality
  field
    com₁
      : ∀ {x}
      → F x Discrete.≡ G x
open _⇒₁_ public

idnᵗᵐ
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → (F : A Π.⇒₀ B)
  → 𝟙.t Π.⇒₀ (F ⇒₁ F)
com₁ (idnᵗᵐ F x) = Discrete.idn x

cmpᵗᵐ
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → {F G H : A Π.⇒₀ B}
  → (G ⇒₁ H) ∐.⊗ (F ⇒₁ G)
  → F ⇒₁ H
com₁ (cmpᵗᵐ (β , α)) = Discrete.cmp (com₁ β , com₁ α)

invᵗᵐ
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → {F G : A Π.⇒₀ B}
  → (F ⇒₁ G) Π.⇒₀ (G ⇒₁ F)
com₁ (invᵗᵐ α) = Discrete.inv (com₁ α)

cmpᵗᵐ-w₀
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → (Hα : (B Π.⇒₀ C) ∐.⊗ (F ⇒₁ G))
  → (∐.π₀ Hα Π.∘ F) ⇒₁ (∐.π₀ Hα Π.∘ G)
com₁ (cmpᵗᵐ-w₀ (H , α)) = H Discrete.$₁ com₁ α

cmpᵗᵐ-w₁_
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {G H : B Π.⇒₀ C}
  → (βF : (G ⇒₁ H) ∐.⊗ (A Π.⇒₀ B))
  → (G Π.∘ ∐.π₁ βF) ⇒₁ (H Π.∘ ∐.π₁ βF)
com₁ (cmpᵗᵐ-w₁ (β , F)) = com₁ β

cmpᵗᵐ-h₀
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → {H K : B Π.⇒₀ C}
  → (βα : (H ⇒₁ K) ∐.⊗ (F ⇒₁ G))
  → (H Π.∘ F) ⇒₁ (K Π.∘ G)
com₁ (cmpᵗᵐ-h₀ {K = K} (β , α)) = Discrete.cmp (K Discrete.$₁ com₁ α , com₁ β)

cmpᵗᵐ-h₁
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → {H K : B Π.⇒₀ C}
  → (βα : (H ⇒₁ K) ∐.⊗ (F ⇒₁ G))
  → (H Π.∘ F) ⇒₁ (K Π.∘ G)
com₁ (cmpᵗᵐ-h₁ {H = H} (β , α)) = Discrete.cmp (com₁ β , H Discrete.$₁ com₁ α)
