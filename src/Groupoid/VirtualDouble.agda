{-# OPTIONS --without-K #-}

module Groupoid.VirtualDouble where

open import Agda.Primitive
open import Common
import Groupoid as G
import Setoid as S
open import Type as T
  using (_,_; *)

module _ ..{ℓ₀ᵒ ℓ₂ᵒ}
  {cell₀ : Set ℓ₀ᵒ}
  (cell₁↔₀ : cell₀ → cell₀ → Set ℓ₂ᵒ)
  where
    data cell₁↔* : (a b : cell₀) → Set (ℓ₀ᵒ ⊔ ℓ₂ᵒ) where
      []
        : ∀ {a}
        → cell₁↔* a a
      _∷_
        : ∀ {a b c}
        → (f  : cell₁↔₀ a b)
        → (f* : cell₁↔* b c)
        → cell₁↔* a c

    _⧺_
      : ∀ {a b c}
      → (p* : cell₁↔* a b)
      → (q* : cell₁↔* b c)
      → cell₁↔* a c
    [] ⧺ q* = q*
    (p ∷ p*) ⧺ q* = p ∷ (p* ⧺ q*)

    module _ ..{ℓ₁ᵒ ℓ₃ᵒ}
      (cell₁↕₀
        : cell₀ → cell₀ → Set ℓ₁ᵒ)
      (cell₂⇓₀
        : ∀ {d↖ d↙ c↗ c↘}
        → (dom↕ : cell₁↕₀ d↖ d↙)
        → (cod↕ : cell₁↕₀ c↗ c↘)
        → (dom↔ : cell₁↔* d↖ c↗)
        → (cod↔ : cell₁↔₀ d↙ c↘)
        → Set ℓ₃ᵒ)
      where
        data cell₂⇓*
          : ∀ {d↖ d↙ c↗ c↘}
          → (dom↕  : cell₁↕₀ d↖ d↙)
          → (cod↕  : cell₁↕₀ c↗ c↘)
          → (dom↔* : cell₁↔* d↖ c↗)
          → (cod↔* : cell₁↔* d↙ c↘)
          → Set (ℓ₀ᵒ ⊔ ℓ₁ᵒ ⊔ ℓ₂ᵒ ⊔ ℓ₃ᵒ)
          where
            []
              : ∀ {a b}
              → {f : cell₁↕₀ a b}
              → cell₂⇓* f f [] []
            _∷_
              : ∀ {d↖ d↙ c↑ c↓ r↗ r↘}
              → {dom↕  : cell₁↕₀ d↖ d↙}
              → {cod↕  : cell₁↕₀ c↑ c↓}
              → {ret↕  : cell₁↕₀ r↗ r↘}
              → {dom←* : cell₁↔* d↖ c↑}
              → {dom→* : cell₁↔* c↑ r↗}
              → {cod←  : cell₁↔₀ d↙ c↓}
              → {cod→* : cell₁↔* c↓ r↘}
              → (α     : cell₂⇓₀ dom↕ cod↕ dom←* cod←)
              → (α*    : cell₂⇓* cod↕ ret↕ dom→* cod→*)
              → cell₂⇓* dom↕ ret↕ (dom←* ⧺ dom→*) (cod← ∷ cod→*)

record t ..{ℓ₀ᵒ ℓ₁ᵒ ℓ₁ʰ ℓ₂ᵒ ℓ₂ʰ ℓ₃ᵒ ℓ₃ʰ}
  : Set (lsuc (ℓ₀ᵒ ⊔ ℓ₁ᵒ ⊔ ℓ₂ᵒ ⊔ ℓ₃ᵒ)
       ⊔ lsuc       (ℓ₁ʰ ⊔ ℓ₂ʰ ⊔ ℓ₃ʰ)) where
  field
    cell₀
      : Set ℓ₀ᵒ
  field
    cell₁↕ˢ
      : (a b : cell₀)
      → S.t Dir.≈ ℓ₁ᵒ ℓ₁ʰ
    idn₁↕
      : ∀ {a}
      → S.𝟙.s⁰ S.Map.⇒₀ᵗ cell₁↕ˢ a a
    cmp₁↕
      : ∀ {a b c}
      → (cell₁↕ˢ b c S.Ten.⊗ cell₁↕ˢ a b) S.Map.⇒₀ᵗ cell₁↕ˢ a c
  field
    cell₁↔ˢ
      : (a b : cell₀)
      → S.t Dir.≈ ℓ₂ᵒ ℓ₂ʰ

  cell₁↕₀
    : (a b : cell₀)
    → Set ℓ₁ᵒ
  cell₁↕₀ a b = S.obj (cell₁↕ˢ a b)

  cell₁↕₁
    : {a b : cell₀}
    → (f₀ f₁ : cell₁↕₀ a b)
    → Set ℓ₁ʰ
  cell₁↕₁ f₀ f₁ = S.homᵗ (cell₁↕ˢ _ _) (f₀ , f₁)

  cell₁↔₀
    : (a b : cell₀)
    → Set ℓ₂ᵒ
  cell₁↔₀ a b = S.obj (cell₁↔ˢ a b)

  cell₁↔₁
    : {a b : cell₀}
    → (f₀ f₁ : cell₁↔₀ a b)
    → Set ℓ₂ʰ
  cell₁↔₁ f₀ f₁ = S.homᵗ (cell₁↔ˢ _ _) (f₀ , f₁)

  idn₁↕₀
    : ∀ {a}
    → cell₁↕₀ a a
  idn₁↕₀ {a} = idn₁↕ {a} S.Map.$₀ _

  .idn₁↕₁
    : ∀ {a}
    → cell₁↕₁ (idn₁↕₀ {a}) (idn₁↕₀ {a})
  idn₁↕₁ {a} = idn₁↕ {a} S.Map.$₁ *

  cmp₁↕₀
    : ∀ {a b c}
    → (g : cell₁↕₀ b c)
    → (f : cell₁↕₀ a b)
    → cell₁↕₀ a c
  cmp₁↕₀ g f = cmp₁↕ S.Map.$₀ (g , f)

  .cmp₁↕₁
    : ∀ {a b c}
    → {g₀ g₁ : cell₁↕₀ b c}
    → {f₀ f₁ : cell₁↕₀ a b}
    → (q : cell₁↕₁ g₀ g₁)
    → (p : cell₁↕₁ f₀ f₁)
    → cell₁↕₁ (cmp₁↕₀ g₀ f₀) (cmp₁↕₀ g₁ f₁)
  cmp₁↕₁ q p = cmp₁↕ S.Map.$₁ (q , p)

  field
    cell₂⇓ˢ
      : ∀ {d↖ d↙ c↗ c↘}
      → (dom↕ : cell₁↕₀ d↖ d↙)
      → (cod↕ : cell₁↕₀ c↗ c↘)
      → (dom↔ : cell₁↔* cell₁↔₀ d↖ c↗)
      → (cod↔ : cell₁↔₀ d↙ c↘)
      → S.t Dir.≈ ℓ₃ᵒ ℓ₃ʰ

  cell₂⇓₀
    : ∀ {d↖ d↙ c↗ c↘}
    → (dom↕ : cell₁↕₀ d↖ d↙)
    → (cod↕ : cell₁↕₀ c↗ c↘)
    → (dom↔ : cell₁↔* cell₁↔₀ d↖ c↗)
    → (cod↔ : cell₁↔₀ d↙ c↘)
    → Set ℓ₃ᵒ
  cell₂⇓₀ dom↕ cod↕ dom↔ cod↔ = S.obj (cell₂⇓ˢ dom↕ cod↕ dom↔ cod↔)

  cell₂⇓₁
    : ∀ {d↖ d↙ c↗ c↘}
    → {dom↕ : cell₁↕₀ d↖ d↙}
    → {cod↕ : cell₁↕₀ c↗ c↘}
    → {dom↔ : cell₁↔* cell₁↔₀ d↖ c↗}
    → {cod↔ : cell₁↔₀ d↙ c↘}
    → (α β : cell₂⇓₀ dom↕ cod↕ dom↔ cod↔)
    → Set ℓ₃ʰ
  cell₂⇓₁ α β = S.homᵗ (cell₂⇓ˢ _ _ _ _) (α , β)

  field
    idn₂
      : ∀ {a b}
      → {p : cell₁↔₀ a b}
      → cell₂⇓₀ idn₁↕₀ idn₁↕₀ (p ∷ []) p
    cmp₂
      : ∀ {d↖ d← d↙ c↗ c→ c↘}
      → {dom↖  : cell₁↕₀ d↖ d←}
      → {dom↙  : cell₁↕₀ d← d↙}
      → {cod↗  : cell₁↕₀ c↗ c→}
      → {cod↘  : cell₁↕₀ c→ c↘}
      → {dom↔* : cell₁↔* cell₁↔₀ d↖ c↗}
      → {cod↔* : cell₁↔* cell₁↔₀ d← c→}
      → {ret↔  : cell₁↔₀ d↙ c↘}
      → (β⇓    : cell₂⇓₀ dom↙ cod↘ cod↔* ret↔)
      → (α⇓*   : cell₂⇓* cell₁↔₀ cell₁↕₀ cell₂⇓₀ dom↖ cod↗ dom↔* cod↔*)
      → cell₂⇓₀ (cmp₁↕₀ dom↙ dom↖) (cmp₁↕₀ cod↘ cod↗) dom↔* ret↔
