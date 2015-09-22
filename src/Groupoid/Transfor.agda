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

idnˢᵐ
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (F : A Π.⇒₀ᵗ B)
  → S.𝟙.s S.Π.⇒₀ᵗ (F ⇒₁ˢ F)
com₁ (S.Π._$₀_ (idnˢᵐ {B = B} F) x) = G.idnˢᵐ B S.Π.$₀ x
com₂ (S.Π._$₁_ (idnˢᵐ {B = B} F) x) = G.idnˢᵐ B S.Π.$₁ x

cmpˢᵐ
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G H : A Π.⇒₀ᵗ B}
  → ((G ⇒₁ˢ H) S.∐.⊗ (F ⇒₁ˢ G)) S.Π.⇒₀ᵗ (F ⇒₁ˢ H)
com₁ (S.Π._$₀_ (cmpˢᵐ {B = B}) (β , α)) = G.cmpˢᵐ B S.Π.$₀ (com₁ β , com₁ α)
com₂ (S.Π._$₁_ (cmpˢᵐ {B = B}) (β , α)) = G.cmpˢᵐ B S.Π.$₁ (com₂ β , com₂ α)

invˢᵐ
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → (F ⇒₁ˢ G) S.Π.⇒₀ᵗ (G ⇒₁ˢ F)
com₁ (S.Π._$₀_ (invˢᵐ {B = B}) α) = G.invˢᵐ B S.Π.$₀ (com₁ α)
com₂ (S.Π._$₁_ (invˢᵐ {B = B}) α) = G.invˢᵐ B S.Π.$₁ (com₂ α)

-- FIXME: cmp-w₀ and cmp-w₀ are problematic because of Hα/βF dependency

-- cmp-w₀
--   : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
--   → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
--   → {F G : A Π.⇒₀ᵗ B}
--   → (Hα : (B Π.⇒₀ᵗ C) T.∐.⊗ (F ⇒₁ᵗ G))
--   → (T.∐.π₀ Hα Π.∘ᵗᵐ F) ⇒₁ᵗ (T.∐.π₀ Hα Π.∘ᵗᵐ G)
-- com₁ (cmp-w₀ (H , α)) = H Π.$₁ com₁ α

-- cmp-w₁
--   : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
--   → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
--   → {G H : B Π.⇒₀ᵗ C}
--   → (βF : (G ⇒₁ᵗ H) T.∐.⊗ (A Π.⇒₀ᵗ B))
--   → (G Π.∘ᵗᵐ T.∐.π₁ βF) ⇒₁ᵗ (H Π.∘ᵗᵐ T.∐.π₁ βF)
-- com₁ (cmp-w₁ (β , F)) = com₁ β

cmpˢᵐ-h₀
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → ((H ⇒₁ˢ K) S.∐.⊗ (F ⇒₁ˢ G)) S.Π.⇒₀ᵗ ((H Π.∘ᵗᵐ F) ⇒₁ˢ (K Π.∘ᵗᵐ G))
com₁ (S.Π._$₀_ (cmpˢᵐ-h₀ {C = C} {K = K}) (β , α)) = G.cmpˢᵐ C S.Π.$₀ (K Π.$₁ com₁ α , com₁ β)
com₂ (S.Π._$₁_ (cmpˢᵐ-h₀ {C = C} {K = K}) (β , α)) = G.cmpˢᵐ C S.Π.$₁ (K Π.$₂ com₂ α , com₂ β)

cmpˢᵐ-h₁
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ} {B : G.t ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ} {C : G.t ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → ((H ⇒₁ˢ K) S.∐.⊗ (F ⇒₁ˢ G)) S.Π.⇒₀ᵗ ((H Π.∘ᵗᵐ F) ⇒₁ˢ (K Π.∘ᵗᵐ G))
com₁ (S.Π._$₀_ (cmpˢᵐ-h₁ {C = C} {H = H}) (β , α)) = G.cmpˢᵐ C S.Π.$₀ (com₁ β , H Π.$₁ com₁ α)
com₂ (S.Π._$₁_ (cmpˢᵐ-h₁ {C = C} {H = H}) (β , α)) = G.cmpˢᵐ C S.Π.$₁ (com₂ β , H Π.$₂ com₂ α)
