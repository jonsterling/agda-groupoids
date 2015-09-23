open import Agda.Primitive
open import Common
import Setoid.Base as S
open import Type as T
  using (_,_)

module Poset.Reasoning ..{ℓᵒ ℓʰ} ⦃ A : S.t Dir.≤ ℓᵒ ℓʰ ⦄ where
  infix  4 _⊢≤_
  infix  3 _∎
  infixr 2 _≤⟨_⟩_
  infix  1 proof_

  data _⊢≤_ (a b : S.obj A) : Set ℓʰ where
    [_] : (a≤b : S.homᵗ A (a , b)) → a ⊢≤ b

  proof_ : ∀ {a b} → a ⊢≤ b → S.homᵗ A (a , b)
  proof [ a≤b ] = a≤b

  _∎ : ∀ a → a ⊢≤ a
  _∎ _ = [ S.idnᵗᵐ A T.𝟙.* ]

  _≤⟨_⟩_ : ∀ a {b c} → S.homᵗ A (a , b) → b ⊢≤ c → a ⊢≤ c
  _ ≤⟨ a≤b ⟩ [ b≤c ] = [ S.cmpᵗᵐ A (b≤c , a≤b) ]
