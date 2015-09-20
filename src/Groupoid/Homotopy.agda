{-# OPTIONS --sized-types --without-K #-}

module Groupoid.Homotopy where

open import Agda.Primitive
import Groupoid.Base as G
import Groupoid.Exponential.Boot as Π
import Setoid as S
open import Type as T
  using (_,_)

infixr 0 _⇒₁_

record _⇒₁_ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  (F G : A Π.⇒₀ᵗ B)
    : Set (ℓ₀ᵒ ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  constructor nat
  field
    com : ∀ {a} → S.obj (G.homˢ B (F Π.$₀ a , G Π.$₀ a))
{-# NO_ETA _⇒₁_ #-}
open _⇒₁_ public

idn
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (F : A Π.⇒₀ᵗ B)
  → T.𝟙.t T.Π.⇒₀ (F ⇒₁ F)
com (idn {B = B} F x) = G.idnˢᵐ B S.Π.$₀ x

cmp
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G H : A Π.⇒₀ᵗ B}
  → (G ⇒₁ H) T.∐.⊗ (F ⇒₁ G)
  → F ⇒₁ H
com (cmp {B = B} (β , α)) = G.cmpˢᵐ B S.Π.$₀ (com β , com α)

inv
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (F ⇒₁ G) T.Π.⇒₀ (G ⇒₁ F)
com (inv {B = B} α) = G.invˢᵐ B S.Π.$₀ (com α)

cmp-w₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (Hα : (B Π.⇒₀ᵗ C) T.∐.⊗ (F ⇒₁ G))
  → (T.∐.π₀ Hα Π.∘ᵗᵐ F) ⇒₁ (T.∐.π₀ Hα Π.∘ᵗᵐ G)
com (cmp-w₀ (H , α)) = H Π.$₁ com α

cmp-w₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {G H : B Π.⇒₀ᵗ C}
  → (βF : (G ⇒₁ H) T.∐.⊗ (A Π.⇒₀ᵗ B))
  → (G Π.∘ᵗᵐ T.∐.π₁ βF) ⇒₁ (H Π.∘ᵗᵐ T.∐.π₁ βF)
com (cmp-w₁ (β , F)) = com β

cmp-h₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (βα : (H ⇒₁ K) T.∐.⊗ (F ⇒₁ G))
  → (H Π.∘ᵗᵐ F) ⇒₁ (K Π.∘ᵗᵐ G)
com (cmp-h₀ {C = C} {K = K} (β , α)) = G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ com α , com β)

cmp-h₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (βα : (H ⇒₁ K) T.∐.⊗ (F ⇒₁ G))
  → (H Π.∘ᵗᵐ F) ⇒₁ (K Π.∘ᵗᵐ G)
com (cmp-h₁ {C = C} {H = H} (β , α)) = G.cmpˢᵐ C S.Π.$₀ (com β , H Π.$₁ com α)
