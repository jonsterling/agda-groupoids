{-# OPTIONS --without-K #-}

module Groupoid.Enriched where

open import Agda.Primitive
open import Common
private
  module G where
    open import Groupoid public
      hiding (module Π)
    module Mon where
      open import Groupoid.Monoidal public
    module Π where
      open Groupoid.Π public
      open import Groupoid.Bifunctor public
import Setoid as S
open import Type as T
  using (_,_)

record t {d} ..{ℓᵒ ℓᵉᵒ ℓᵉˢᵒ ℓᵉˢʰ}
  {𝒱 : G.t d ℓᵉᵒ ℓᵉˢᵒ ℓᵉˢʰ}
  (M : G.Mon.t 𝒱)
    : Set (lsuc (ℓᵒ ⊔ ℓᵉᵒ ⊔ ℓᵉˢᵒ ⊔ ℓᵉˢʰ)) where
  no-eta-equality
  open G.Mon.t M
  open G.TF
  field
    obj
      : Set ℓᵒ
    hom
      : obj T.∐.⊗ obj → G.obj 𝒱
    idn
      : ∀ {a}
      → G.hom₀ 𝒱 𝟙 (hom (a , a))
    cmp
      : ∀ {a b c}
      → G.hom₀ 𝒱 (hom (b , c) ⊗₀ hom (a , b)) (hom (a , c))
  field
    idn-lhs
      : ∀ {a b}
      → G.hom₁ 𝒱
          {𝟙 ⊗₀ hom (a , b)}
          {hom (a , b)}
      G.⊢ 𝒱 [ cmp ∘₀ (idn ⊗₁ G.idn₀ 𝒱) ]
      ---------------------------------- ≃₁
      ⟨ ƛ ⇒⟩₁

    idn-rhs
      : ∀ {a b}
      → G.hom₁ 𝒱
          {hom (a , b) ⊗₀ 𝟙}
          {hom (a , b)}
      G.⊢ 𝒱 [ cmp ∘₀ (G.idn₀ 𝒱 ⊗₁ idn) ]
      ------- ≃₁
      ⟨ ρ ⇒⟩₁

    cmp-ass
      : ∀ {a b c d}
      → G.hom₁ 𝒱
          {(hom (c , d) ⊗₀ hom (b , c)) ⊗₀ hom (a , b)}
          {hom (a , d)}
      G.⊢ 𝒱 [ G.⊢ 𝒱 [ cmp ∘₀ (G.idn₀ 𝒱 ⊗₁ cmp) ] ∘₀ ⟨ α ⇒⟩₁ ]
      ------------------------------------------------------- ≃₁
      G.⊢ 𝒱 [ cmp ∘₀ (cmp ⊗₁ G.idn₀ 𝒱) ]
