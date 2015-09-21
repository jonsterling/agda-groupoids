{-# OPTIONS --without-K #-}

module Setoid.Transfor where

open import Agda.Primitive
import Setoid.Base as S
import Setoid.Exponential.Boot as Π
import Setoid.Path as Path
import Setoid.Terminal as 𝟙
open import Type as T
  using (_,_)

infixr 0 _⇒₁_

record _⇒₁_ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  (F G : A Π.⇒₀ᵗ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ʰ) where
  no-eta-equality
  constructor nat₁
  field
    com₁
      : ∀ {a}
      → S.homᵗ B (F Π.$₀ a , G Π.$₀ a)
open _⇒₁_ public

com₁′
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → ∀ {a} (α : F ⇒₁ G) → S.homᵗ B (F Π.$₀ a , G Π.$₀ a)
com₁′ α = com₁ α

idn
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → (F : A Π.⇒₀ᵗ B)
  → T.𝟙.t T.Π.⇒₀ (F ⇒₁ F)
com₁ (idn {B = B} F x) = S.idnᵗᵐ B x

cmp
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {F G H : A Π.⇒₀ᵗ B}
  → (G ⇒₁ H) T.∐.⊗ (F ⇒₁ G)
  → F ⇒₁ H
com₁ (cmp {B = B} (β , α)) = S.cmpᵗᵐ B (com₁ β , com₁ α)

inv
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (F ⇒₁ G) T.Π.⇒₀ (G ⇒₁ F)
com₁ (inv {B = B} α) = S.invᵗᵐ B (com₁ α)

cmp-w₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ }
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (Hα : (B Π.⇒₀ᵗ C) T.∐.⊗ (F ⇒₁ G))
  → (T.∐.π₀ Hα Π.∘ᵗᵐ F) ⇒₁ (T.∐.π₀ Hα Π.∘ᵗᵐ G)
com₁ (cmp-w₀ (H , α)) = H Π.$₁ com₁ α

cmp-w₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → {G H : B Π.⇒₀ᵗ C}
  → (βF : (G ⇒₁ H) T.∐.⊗ (A Π.⇒₀ᵗ B))
  → (G Π.∘ᵗᵐ T.∐.π₁ βF) ⇒₁ (H Π.∘ᵗᵐ T.∐.π₁ βF)
com₁ (cmp-w₁ (β , F)) = com₁ β

cmp-h₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (βα : (H ⇒₁ K) T.∐.⊗ (F ⇒₁ G))
  → (H Π.∘ᵗᵐ F) ⇒₁ (K Π.∘ᵗᵐ G)
com₁ (cmp-h₀ {C = C} {K = K} (β , α)) = S.cmpᵗᵐ C (K Π.$₁ com₁ α , com₁ β)

cmp-h₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t ℓ₀ᵒ ℓ₀ʰ} {B : S.t ℓ₁ᵒ ℓ₁ʰ} {C : S.t ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (βα : (H ⇒₁ K) T.∐.⊗ (F ⇒₁ G))
  → (H Π.∘ᵗᵐ F) ⇒₁ (K Π.∘ᵗᵐ G)
com₁ (cmp-h₁ {C = C} {H = H} (β , α)) = S.cmpᵗᵐ C (com₁ β , H Π.$₁ com₁ α)
