open import Agda.Primitive
open import Common
import Category.Core.Base as C
import Setoid as S
open import Type as T
  using (_,_)

module Category.Reasoning ..{ℓᵒ ℓˢᵒ ℓˢʰ} (A : C.t ℓᵒ ℓˢᵒ ℓˢʰ) where
  infix  4 _⊢≤_
  infix  3 _∎
  infixr 2 _≤⟨_⟩_
  infix  1 proof_

  data _⊢≤_ (a b : C.obj A) : Set ℓˢᵒ where
    [_] : S.obj (C.homˢ A (a , b)) → a ⊢≤ b

  proof_ : ∀ {a b} → a ⊢≤ b → S.obj (C.homˢ A (a , b))
  proof [ a≤b ] = a≤b

  _∎ : ∀ a → a ⊢≤ a
  _∎ _ = [ C.idnˢᵐ A S.Π.$₀ T.𝟙.* ]

  _≤⟨_⟩_ : ∀ a {b c} → S.obj (C.homˢ A (a , b)) → b ⊢≤ c → a ⊢≤ c
  _ ≤⟨ a≤b ⟩ [ b≤c ] = [ C.cmpˢᵐ A S.Π.$₀ (b≤c , a≤b) ]
