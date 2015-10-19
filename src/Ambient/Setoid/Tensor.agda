{-# OPTIONS --without-K #-}

module Ambient.Setoid.Tensor where

open import Agda.Primitive
import Ambient.Setoid.Base as S
open import Ambient.Setoid.Map
open import Ambient.Setoid.Tensor.Boot public
open import Type as T

π₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
  → (A ⊗ B) ⇒₀ᵗ A
_$₀_ π₀ = π⁰₀
_$₁_ π₀ = π⁰₀

π₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
  → (A ⊗ B) ⇒₀ᵗ B
_$₀_ π₁ = π¹₀
_$₁_ π₁ = π¹₀

⟨-,-⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {X : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
  → {B : S.𝔊₁ d ℓ₂ᵒ ℓ₂ʰ}
  → ((X ⇒₀ˢ A) ⊗ (X ⇒₀ˢ B)) ⇒₀ᵗ (X ⇒₀ˢ A ⊗ B)
_$₀_ (_$₀_ ⟨-,-⟩ FG) =
  ⟨ π⁰₀ FG $₀_ ,₀ π¹₀ FG $₀_ ⟩
_$₁_ (_$₀_ ⟨-,-⟩ FG) =
  ⟨ π⁰₀ FG $₁_ ,₀ π¹₀ FG $₁_ ⟩
com₁ (_$₁_ ⟨-,-⟩ x) =
  ⟨ com₁ᵗ′ ×₀ com₁ᵗ′ ⟩ x

⟨-⊗-⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ ℓ₃ᵒ ℓ₃ʰ}
  → {X₀ : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
  → {X₁ : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.𝔊₁ d ℓ₂ᵒ ℓ₂ʰ}
  → {B : S.𝔊₁ d ℓ₃ᵒ ℓ₃ʰ}
  → ((X₀ ⇒₀ˢ A) ⊗ (X₁ ⇒₀ˢ B)) ⇒₀ᵗ ((X₀ ⊗ X₁) ⇒₀ˢ (A ⊗ B))
_$₀_ (_$₀_ ⟨-⊗-⟩ FG) =
  ⟨ π⁰₀ FG $₀_ ×₀ π¹₀ FG $₀_ ⟩
_$₁_ (_$₀_ ⟨-⊗-⟩ FG) =
  ⟨ π⁰₀ FG $₁_ ×₀ π¹₀ FG $₁_ ⟩
com₁ (_$₁_ ⟨-⊗-⟩ x) =
  ⟨ com₁ᵗ′ ×₀ com₁ᵗ′ ⟩ x

-- ap-lhs₀
--   : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
--   → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
--   → {B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
--   → {C : S.𝔊₁ d ℓ₂ᵒ ℓ₂ʰ}
--   → (F : A ⊗ B ⇒₀ᵗ C)
--   → (a : S.obj A)
--   → B ⇒₀ᵗ C
-- _$₀_ (ap-lhs₀ F a) = T.Ten.ap-lhs (F $₀_) a
-- _$₁_ (ap-lhs₀ {A = A} F a) = T.Ten.ap-lhs (F $₁_) (S.idnᵗ A _)

-- ap-rhs₀
--   : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
--   → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
--   → {B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
--   → {C : S.𝔊₁ d ℓ₂ᵒ ℓ₂ʰ}
--   → (F : A ⊗ B ⇒₀ᵗ C)
--   → (b : S.obj B)
--   → A ⇒₀ᵗ C
-- _$₀_ (ap-rhs₀ F b) = T.Ten.ap-rhs (F $₀_) b
-- _$₁_ (ap-rhs₀ {B = B} F b) = T.Ten.ap-rhs (F $₁_) (S.idnᵗ B _)

-- ap-lhs₁
--   : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
--   → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
--   → {B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
--   → {C : S.𝔊₁ d ℓ₂ᵒ ℓ₂ʰ}
--   → (F : A ⊗ B ⇒₀ᵗ C)
--   → {a₀ a₁ : S.obj A}
--   → (f : S.homᵗ A (a₀ , a₁))
--   → ap-lhs₀ F a₀ ⇒₁ ap-lhs₀ F a₁
-- com₁ (ap-lhs₁ {B = B} F f) = F $₁ (f , S.idnᵗ B _)

-- ap-rhs₁
--   : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
--   → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
--   → {B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
--   → {C : S.𝔊₁ d ℓ₂ᵒ ℓ₂ʰ}
--   → (F : A ⊗ B ⇒₀ᵗ C)
--   → {b₀ b₁ : S.obj B}
--   → (f : S.homᵗ B (b₀ , b₁))
--   → ap-rhs₀ F b₀ ⇒₁ ap-rhs₀ F b₁
-- com₁ (ap-rhs₁ {A = A} F f) = F $₁ (S.idnᵗ A _ , f)

-- curry
--   : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
--   → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
--   → {B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
--   → {C : S.𝔊₁ d ℓ₂ᵒ ℓ₂ʰ}
--   → (F : A ⊗ B ⇒₀ᵗ C)
--   → A ⇒₀ᵗ (B ⇒₀ˢ C)
-- _$₀_ (curry F) = ap-lhs₀ F
-- _$₁_ (curry F) = ap-lhs₁ F

-- uncurry
--   : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
--   → {A : S.𝔊₁ d ℓ₀ᵒ ℓ₀ʰ}
--   → {B : S.𝔊₁ d ℓ₁ᵒ ℓ₁ʰ}
--   → {C : S.𝔊₁ d ℓ₂ᵒ ℓ₂ʰ}
--   → (F : A ⇒₀ᵗ (B ⇒₀ˢ C))
--   → A ⊗ B ⇒₀ᵗ C
-- _$₀_ (uncurry F) =
--   T.Ten.uncurry _$₀_ T.Map.∘ T.Ten.⟨ (F $₀_) ⊗₀ T.Map.idn ⟩
-- _$₁_ (uncurry {C = C} F) (f₀ , f₁) =
--   S.cmpᵗ C (com₁ (F $₁ f₀) , (F $₀ _) $₁ f₁)
