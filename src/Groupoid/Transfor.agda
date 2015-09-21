{-# OPTIONS --without-K #-}

module Groupoid.Transfor where

open import Agda.Primitive
import Groupoid.Base as G
import Groupoid.Exponential.Boot as Π
import Setoid as S
open import Type as T
  using (_,_)

infixr 0 _⇒₁ᵗ_

record _⇒₁ᵗ_ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  (F G : A Π.⇒₀ᵗ B)
    : Set (ℓ₀ᵒ ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  constructor nat₁
  field
    com₁
      : ∀ {a}
      → S.obj (G.homˢ B (F Π.$₀ a , G Π.$₀ a))
open _⇒₁ᵗ_ public

record _⇒₂_ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {F G : A Π.⇒₀ᵗ B}
  (α β : F ⇒₁ᵗ G)
    : Set (ℓ₀ᵒ ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  constructor nat₂
  field
    .com₂
      : ∀ {a}
      → S.homᵗ (G.homˢ B (F Π.$₀ a , G Π.$₀ a)) (com₁ α {a} , com₁ β {a})
open _⇒₂_ public

_⇒₁ˢ_ : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (F G : A Π.⇒₀ᵗ B)
  → S.t _ _
S.obj (_⇒₁ˢ_ F G) =
  F ⇒₁ᵗ G
S.homᵗ (_⇒₁ˢ_ F G) =
  λ {(α , β) → α ⇒₂ β}
com₂ (S.idnᵗᵐ (_⇒₁ˢ_ {B = B} F G) _) = λ {a} →
  S.idnᵗᵐ (G.homˢ B (F Π.$₀ a , G Π.$₀ a)) _
com₂ (S.cmpᵗᵐ (_⇒₁ˢ_ {B = B} F G) (g⇒₂ , f⇒₂)) = λ {a} →
  S.cmpᵗᵐ (G.homˢ B (F Π.$₀ a , G Π.$₀ a))
    (com₂ g⇒₂ {a} , com₂ f⇒₂ {a})
com₂ (S.invᵗᵐ (_⇒₁ˢ_ {B = B} F G) f⇒₂) = λ {a} →
  S.invᵗᵐ (G.homˢ B (F Π.$₀ a , G Π.$₀ a))
    (com₂ f⇒₂ {a})

-- FIXME: the following should all be setoid morphisms now…

idn
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (F : A Π.⇒₀ᵗ B)
  → T.𝟙.t T.Π.⇒₀ (F ⇒₁ᵗ F)
com₁ (idn {B = B} F x) = G.idnˢᵐ B S.Π.$₀ x

cmp
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G H : A Π.⇒₀ᵗ B}
  → (G ⇒₁ᵗ H) T.∐.⊗ (F ⇒₁ᵗ G)
  → F ⇒₁ᵗ H
com₁ (cmp {B = B} (β , α)) = G.cmpˢᵐ B S.Π.$₀ (com₁ β , com₁ α)

inv
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (F ⇒₁ᵗ G) T.Π.⇒₀ (G ⇒₁ᵗ F)
com₁ (inv {B = B} α) = G.invˢᵐ B S.Π.$₀ (com₁ α)

cmp-w₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (Hα : (B Π.⇒₀ᵗ C) T.∐.⊗ (F ⇒₁ᵗ G))
  → (T.∐.π₀ Hα Π.∘ᵗᵐ F) ⇒₁ᵗ (T.∐.π₀ Hα Π.∘ᵗᵐ G)
com₁ (cmp-w₀ (H , α)) = H Π.$₁ com₁ α

cmp-w₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {G H : B Π.⇒₀ᵗ C}
  → (βF : (G ⇒₁ᵗ H) T.∐.⊗ (A Π.⇒₀ᵗ B))
  → (G Π.∘ᵗᵐ T.∐.π₁ βF) ⇒₁ᵗ (H Π.∘ᵗᵐ T.∐.π₁ βF)
com₁ (cmp-w₁ (β , F)) = com₁ β

cmp-h₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (βα : (H ⇒₁ᵗ K) T.∐.⊗ (F ⇒₁ᵗ G))
  → (H Π.∘ᵗᵐ F) ⇒₁ᵗ (K Π.∘ᵗᵐ G)
com₁ (cmp-h₀ {C = C} {K = K} (β , α)) = G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ com₁ α , com₁ β)

cmp-h₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (βα : (H ⇒₁ᵗ K) T.∐.⊗ (F ⇒₁ᵗ G))
  → (H Π.∘ᵗᵐ F) ⇒₁ᵗ (K Π.∘ᵗᵐ G)
com₁ (cmp-h₁ {C = C} {H = H} (β , α)) = G.cmpˢᵐ C S.Π.$₀ (com₁ β , H Π.$₁ com₁ α)
