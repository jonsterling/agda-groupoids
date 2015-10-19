{-# OPTIONS --without-K #-}

module Ambient.Setoid.Map where

open import Agda.Primitive
import Ambient.Setoid.Base as S
import Ambient.Setoid.Map.Boot as Map
open import Ambient.Setoid.Tensor.Boot as Ten
import Ambient.Setoid.Terminal as 𝟙
open import Type as T
  using (_,_)

infixr 2 _⇒₀ˢ_
infixr 2 _∘₀_
infixr 0 _⇒₁_
infixr 2 _∘₁_

record _⇒₁_
  {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  (F G : A Map.⇒₀ᵗ B)
    : Set (ℓ₀ᵒ ⊔ ℓ₁ʰ) where
  no-eta-equality
  field
    .com₁
      : ∀ {a}
      → S.homᵗ B (F Map.$₀ a , G Map.$₀ a)
open _⇒₁_ public

.com₁ᵗ′
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {F G : A Map.⇒₀ᵗ B}
  → ∀ {a} (α : F ⇒₁ G)
  → S.homᵗ B (F Map.$₀ a , G Map.$₀ a)
com₁ᵗ′ α = com₁ α

idn₁ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → (F : A Map.⇒₀ᵗ B)
  → T.𝟙.t T.Map.⇒₀ (F ⇒₁ F)
com₁ (idn₁ᵗ {B = B} F x) = S.idnᵗ B x

cmp₁ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {F G H : A Map.⇒₀ᵗ B}
  → (G ⇒₁ H) T.Ten.⊗ (F ⇒₁ G)
  → F ⇒₁ H
com₁ (cmp₁ᵗ {B = B} (β , α)) =
  S.cmpᵗ B (com₁ β , com₁ α)

inv₁ᵗ
  : ∀ ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t S.Dir.≈ ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t S.Dir.≈ ℓ₁ᵒ ℓ₁ʰ}
  → {F G : A Map.⇒₀ᵗ B}
  → (F ⇒₁ G) T.Map.⇒₀ (G ⇒₁ F)
com₁ (inv₁ᵗ {B = B} α) = S.invᵗ B (com₁ α)

cmp₁ᵗ-w₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ }
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Map.⇒₀ᵗ B}
  → (Hα : (B Map.⇒₀ᵗ C) T.Ten.⊗ (F ⇒₁ G))
  → (T.Ten.π₀ Hα Map.∘₀ᵗ F) ⇒₁ (T.Ten.π₀ Hα Map.∘₀ᵗ G)
com₁ (cmp₁ᵗ-w₀ (H , α)) = H Map.$₁ com₁ α

cmp₁ᵗ-w₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {G H : B Map.⇒₀ᵗ C}
  → (βF : (G ⇒₁ H) T.Ten.⊗ (A Map.⇒₀ᵗ B))
  → (G Map.∘₀ᵗ T.Ten.π₁ βF) ⇒₁ (H Map.∘₀ᵗ T.Ten.π₁ βF)
com₁ (cmp₁ᵗ-w₁ (β , F)) = com₁ β

cmp₁ᵗ-h₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Map.⇒₀ᵗ B}
  → {H K : B Map.⇒₀ᵗ C}
  → (βα : (H ⇒₁ K) T.Ten.⊗ (F ⇒₁ G))
  → (H Map.∘₀ᵗ F) ⇒₁ (K Map.∘₀ᵗ G)
com₁ (cmp₁ᵗ-h₀ {C = C} {K = K} (β , α)) =
  S.cmpᵗ C (K Map.$₁ com₁ α , com₁ β)

cmp₁ᵗ-h₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Map.⇒₀ᵗ B}
  → {H K : B Map.⇒₀ᵗ C}
  → (βα : (H ⇒₁ K) T.Ten.⊗ (F ⇒₁ G))
  → (H Map.∘₀ᵗ F) ⇒₁ (K Map.∘₀ᵗ G)
com₁ (cmp₁ᵗ-h₁ {C = C} {H = H} (β , α)) =
  S.cmpᵗ C (com₁ β , H Map.$₁ com₁ α)

_⇒₀ˢ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → (A : S.t d ℓ₀ᵒ ℓ₀ʰ)
  → (B : S.t d ℓ₁ᵒ ℓ₁ʰ)
  → S.t d _ _
S.obj (A ⇒₀ˢ B) =
  A Map.⇒₀ᵗ B
S.homᵗ (A ⇒₀ˢ B) =
  λ {(F , G) → F ⇒₁ G}
S.idnᵗ (A ⇒₀ˢ B) =
  idn₁ᵗ _
S.cmpᵗ (A ⇒₀ˢ B) =
  cmp₁ᵗ
S.invᵗ (_⇒₀ˢ_ {S.Dir.≤} A B) =
  _
S.invᵗ (_⇒₀ˢ_ {S.Dir.≈} A B) =
  inv₁ᵗ

idn₀ˢ
  : ∀ {d} ..{ℓᵒ ℓʰ}
  → {A : S.t d ℓᵒ ℓʰ}
  → 𝟙.s Map.⇒₀ᵗ (A ⇒₀ˢ A)
Map._$₀_ idn₀ˢ = Map.idn₀ᵗ
Map._$₁_ idn₀ˢ = idn₁ᵗ _

cmp₀ˢ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ˢ C) Ten.⊗ (A ⇒₀ˢ B) Map.⇒₀ᵗ (A ⇒₀ˢ C)
Map._$₀_ cmp₀ˢ = Map.cmp₀ᵗ
Map._$₁_ cmp₀ˢ = cmp₁ᵗ-h₁

!ˢ : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → S.obj A → (B Map.⇒₀ᵗ A)
Map._$₀_ (!ˢ a) = T.Map.elm a
Map._$₁_ (!ˢ {A = A} _) = T.Map.elm (S.idnᵗ A T.𝟙.*)

_∘₀_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (G : B Map.⇒₀ᵗ C)
  → (F : A Map.⇒₀ᵗ B)
  → (A Map.⇒₀ᵗ C)
G ∘₀ F = G Map.∘₀ᵗ F

._∘₁_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Map.⇒₀ᵗ B}
  → {H K : B Map.⇒₀ᵗ C}
  → (β : H ⇒₁ K)
  → (α : F ⇒₁ G)
  → (H Map.∘₀ᵗ F) ⇒₁ (K Map.∘₀ᵗ G)
β ∘₁ α = cmp₀ˢ Map.$₁ (β , α)

open import Ambient.Setoid.Map.Boot public
