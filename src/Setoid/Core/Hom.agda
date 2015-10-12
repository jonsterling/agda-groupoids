{-# OPTIONS --without-K #-}

module Setoid.Core.Hom where

open import Agda.Primitive
import Setoid.Core.Base as S
import Setoid.Core.Hom.Boot as Π
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
  A Π.⇒₀ᵗ B
S.homᵗ (A ⇒₀ˢ B) =
  λ {(F , G) → F TF.⇒₁ G}
S.idnᵗ (A ⇒₀ˢ B) =
  TF.idn₁ᵗ _
S.cmpᵗ (A ⇒₀ˢ B) =
  TF.cmp₁ᵗ
S.invᵗ (_⇒₀ˢ_ {S.Dir.≤} A B) =
  _
S.invᵗ (_⇒₀ˢ_ {S.Dir.≈} A B) =
  TF.inv₁ᵗ

idn₀ˢ
  : ∀ {d} ..{ℓᵒ ℓʰ}
  → {A : S.t d ℓᵒ ℓʰ}
  → 𝟙.s Π.⇒₀ᵗ (A ⇒₀ˢ A)
Π._$₀_ idn₀ˢ = Π.idn₀ᵗ
Π._$₁_ idn₀ˢ = TF.idn₁ᵗ _

cmp₀ˢ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (B ⇒₀ˢ C) ∐.⊗ (A ⇒₀ˢ B) Π.⇒₀ᵗ (A ⇒₀ˢ C)
Π._$₀_ cmp₀ˢ = Π.cmp₀ᵗ
Π._$₁_ cmp₀ˢ = TF.cmp₁ᵗ-h₁

!ˢ : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → S.obj A → (B Π.⇒₀ᵗ A)
Π._$₀_ (!ˢ a) = T.Π.! a
Π._$₁_ (!ˢ {A = A} _) = T.Π.! (S.idnᵗ A T.𝟙.*)

_∘₀_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (G : B Π.⇒₀ᵗ C)
  → (F : A Π.⇒₀ᵗ B)
  → (A Π.⇒₀ᵗ C)
G ∘₀ F = G Π.∘₀ᵗ F

._∘₁_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {F G : A Π.⇒₀ᵗ B}
  → {H K : B Π.⇒₀ᵗ C}
  → (β : H TF.⇒₁ K)
  → (α : F TF.⇒₁ G)
  → (H Π.∘₀ᵗ F) TF.⇒₁ (K Π.∘₀ᵗ G)
β ∘₁ α = cmp₀ˢ Π.$₁ (β , α)

open import Setoid.Core.Hom.Boot public
