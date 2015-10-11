{-# OPTIONS --without-K #-}

module Setoid.Core.Tensor where

open import Agda.Primitive
import Setoid.Core.Base as S
open import Setoid.Core.Hom as Π
import Setoid.Core.Homotopy as TF
open import Setoid.Core.Tensor.Boot public
open import Type as T
  using (_,_)

π₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → (A ⊗ B) Π.⇒₀ᵗ A
_$₀_ π₀ = T.∐.π₀
_$₁_ π₀ = T.∐.π₀

π₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → (A ⊗ B) Π.⇒₀ᵗ B
_$₀_ π₁ = T.∐.π₁
_$₁_ π₁ = T.∐.π₁

⟨-,-⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {X : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {A : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {B : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → ((X Π.⇒₀ˢ A) ⊗ (X Π.⇒₀ˢ B)) Π.⇒₀ᵗ (X Π.⇒₀ˢ A ⊗ B)
_$₀_ (_$₀_ ⟨-,-⟩ FG) =
  T.∐.⟨ T.∐.π₀ FG $₀_ , T.∐.π₁ FG $₀_ ⟩
_$₁_ (_$₀_ ⟨-,-⟩ FG) =
  T.∐.⟨ T.∐.π₀ FG $₁_ , T.∐.π₁ FG $₁_ ⟩
TF.com₁ (_$₁_ ⟨-,-⟩ x) =
  T.∐.⟨ TF.com₁ᵗ′ ⊗ TF.com₁ᵗ′ ⟩ x

⟨-⊗-⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ ℓ₃ᵒ ℓ₃ʰ}
  → {X₀ : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {X₁ : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {A : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → {B : S.t d ℓ₃ᵒ ℓ₃ʰ}
  → ((X₀ Π.⇒₀ˢ A) ⊗ (X₁ Π.⇒₀ˢ B)) Π.⇒₀ᵗ ((X₀ ⊗ X₁) Π.⇒₀ˢ (A ⊗ B))
_$₀_ (_$₀_ ⟨-⊗-⟩ FG) =
  T.∐.⟨ T.∐.π₀ FG $₀_ ⊗ T.∐.π₁ FG $₀_ ⟩
_$₁_ (_$₀_ ⟨-⊗-⟩ FG) =
  T.∐.⟨ T.∐.π₀ FG $₁_ ⊗ T.∐.π₁ FG $₁_ ⟩
TF.com₁ (_$₁_ ⟨-⊗-⟩ x) =
  T.∐.⟨ TF.com₁ᵗ′ ⊗ TF.com₁ᵗ′ ⟩ x

ap-lhs₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (F : A ⊗ B Π.⇒₀ᵗ C)
  → (a : S.obj A)
  → B Π.⇒₀ᵗ C
_$₀_ (ap-lhs₀ F a) = T.∐.ap-lhs (F $₀_) a
_$₁_ (ap-lhs₀ {A = A} F a) = T.∐.ap-lhs (F $₁_) (S.idnᵗ A _)

ap-rhs₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (F : A ⊗ B Π.⇒₀ᵗ C)
  → (b : S.obj B)
  → A Π.⇒₀ᵗ C
_$₀_ (ap-rhs₀ F b) = T.∐.ap-rhs (F $₀_) b
_$₁_ (ap-rhs₀ {B = B} F b) = T.∐.ap-rhs (F $₁_) (S.idnᵗ B _)

ap-lhs₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (F : A ⊗ B Π.⇒₀ᵗ C)
  → {a₀ a₁ : S.obj A}
  → (f : S.homᵗ A (a₀ , a₁))
  → ap-lhs₀ F a₀ TF.⇒₁ ap-lhs₀ F a₁
TF.com₁ (ap-lhs₁ {B = B} F f) = F $₁ (f , S.idnᵗ B _)

ap-rhs₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (F : A ⊗ B Π.⇒₀ᵗ C)
  → {b₀ b₁ : S.obj B}
  → (f : S.homᵗ B (b₀ , b₁))
  → ap-rhs₀ F b₀ TF.⇒₁ ap-rhs₀ F b₁
TF.com₁ (ap-rhs₁ {A = A} F f) = F $₁ (S.idnᵗ A _ , f)

curry
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
  → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
  → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
  → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
  → (F : A ⊗ B Π.⇒₀ᵗ C)
  → A Π.⇒₀ᵗ (B Π.⇒₀ˢ C)
_$₀_ (curry F) = ap-lhs₀ F
_$₁_ (curry F) = ap-lhs₁ F

-- FIXME: We can't define `uncurry` unless transformations are
-- relevant. However, if we make them relevant then we also need to
-- make the groupoid laws relevant in order to define the Yoneda
-- embedding (among other things).

-- uncurry
--   : ∀ {d} ..{ℓ₀ᵒ ℓ₀ʰ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ}
--   → {A : S.t d ℓ₀ᵒ ℓ₀ʰ}
--   → {B : S.t d ℓ₁ᵒ ℓ₁ʰ}
--   → {C : S.t d ℓ₂ᵒ ℓ₂ʰ}
--   → (F : A Π.⇒₀ᵗ (B Π.⇒₀ˢ C))
--   → A ⊗ B Π.⇒₀ᵗ C
-- _$₀_ (uncurry F) =
--   T.∐.uncurry _$₀_ T.Π.∘ T.∐.⟨ (F $₀_) ⊗ T.Π.idn ⟩
-- _$₁_ (uncurry {C = C} F) (f₀ , f₁) =
--   S.cmpᵗ C (TF.com₁ (F $₁ f₀) , (F $₀ _) $₁ f₁)

