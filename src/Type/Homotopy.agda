{-# OPTIONS --sized-types --without-K #-}

module Type.Homotopy where

open import Agda.Primitive
import Type.Base as T
import Type.Exponential as Π
import Type.Path as Path
  renaming (t to _≡_)
open import Type.Tensor as ∐
  using (_,_)
import Type.Terminal as 𝟙

infixr 0 _⇒₁_

record _⇒₁_ ..{ℓ₀ᵒ ℓ₁ᵒ}
  {A : T.t ℓ₀ᵒ}
  {B : T.t ℓ₁ᵒ}
  (F G : A Π.⇒₀ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ᵒ) where
  constructor nat
  field
    com₁
      : ∀ {x}
      → F x Path.≡ G x
{-# NO_ETA _⇒₁_ #-}
open _⇒₁_ public

idn
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → (F : A Π.⇒₀ B)
  → 𝟙.t Π.⇒₀ (F ⇒₁ F)
com₁ (idn F x) = Path.idn x

cmp
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → {F G H : A Π.⇒₀ B}
  → (G ⇒₁ H) ∐.⊗ (F ⇒₁ G)
  → F ⇒₁ H
com₁ (cmp (β , α)) = Path.cmp (com₁ β , com₁ α)

inv
  : ∀ {ℓ₀ᵒ ℓ₁ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ}
  → {F G : A Π.⇒₀ B}
  → (F ⇒₁ G) Π.⇒₀ (G ⇒₁ F)
com₁ (inv α) = Path.inv (com₁ α)

cmp-w₀
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → (Hα : (B Π.⇒₀ C) ∐.⊗ (F ⇒₁ G))
  → (∐.π₀ Hα Π.∘ F) ⇒₁ (∐.π₀ Hα Π.∘ G)
com₁ (cmp-w₀ (H , α)) = H Path.$₁ com₁ α

cmp-w₁_
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {G H : B Π.⇒₀ C}
  → (βF : (G ⇒₁ H) ∐.⊗ (A Π.⇒₀ B))
  → (G Π.∘ ∐.π₁ βF) ⇒₁ (H Π.∘ ∐.π₁ βF)
com₁ (cmp-w₁ (β , F)) = com₁ β

cmp-h₀
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → {H K : B Π.⇒₀ C}
  → (βα : (H ⇒₁ K) ∐.⊗ (F ⇒₁ G))
  → (H Π.∘ F) ⇒₁ (K Π.∘ G)
com₁ (cmp-h₀ {K = K} (β , α)) = Path.cmp (K Path.$₁ com₁ α , com₁ β)

cmp-h₁
  : ∀ ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₂ᵒ}
  → {A : T.t ℓ₀ᵒ} {B : T.t ℓ₁ᵒ} {C : T.t ℓ₂ᵒ}
  → {F G : A Π.⇒₀ B}
  → {H K : B Π.⇒₀ C}
  → (βα : (H ⇒₁ K) ∐.⊗ (F ⇒₁ G))
  → (H Π.∘ F) ⇒₁ (K Π.∘ G)
com₁ (cmp-h₁ {H = H} (β , α)) = Path.cmp (com₁ β , H Path.$₁ com₁ α)
