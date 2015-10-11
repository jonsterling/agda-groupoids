{-# OPTIONS --without-K #-}

module Groupoid.Monoidal where

open import Agda.Primitive
module G where
  open import Groupoid public
    hiding (module Π)
  module Π where
    open Groupoid.Π public
    open import Groupoid.Bifunctor public
import Setoid as S
open import Type as T
  using (_,_)

record t {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  (A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ)
    : Set (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ) where
  no-eta-equality
  field
    ⊗ : G.Π.:⟨ A , A ⟩⇒₀ᵗ A
    𝟙 : G.obj A
  field
    ƛ
      : (⊗ G.Π.∘₀ᵗ G.∐.⟨-,-⟩ G.Π.$₀ (G.Π.!ᵍ 𝟙 , G.Π.idn₀ᵗ T.𝟙.*))
      G.TF.⇔₁ G.Π.idn₀ᵗ T.𝟙.*
    ρ
      : G.Π.idn₀ᵗ T.𝟙.*
      G.TF.⇔₁ (⊗ G.Π.∘₀ᵗ G.∐.⟨-,-⟩ G.Π.$₀ (G.Π.idn₀ᵗ T.𝟙.* , G.Π.!ᵍ 𝟙))
    α
      :  (⊗ G.Π.∘₀ᵗ G.∐.⟨-⊗-⟩ G.Π.$₀ (⊗ , G.Π.idn₀ᵗ T.𝟙.*))
      G.TF.⇔₁
        ((⊗ G.Π.∘₀ᵗ G.∐.⟨-⊗-⟩ G.Π.$₀ (G.Π.idn₀ᵗ T.𝟙.* , ⊗))
            G.Π.∘₀ᵗ {!!})
  field
    .tri
      : ∀ {a₀ a₁ : G.obj A}
      → S.homᵗ (G.homˢ A _)
        ( G.cmpˢ A S.Π.$₀
          ( ⊗ G.Π.$₁ (G.idnˢ A S.Π.$₀ T.𝟙.* , G.TF.com₁ (G.TF.fwd ƛ) {a₁})
          , G.TF.com₁ (G.TF.fwd α))
        , ⊗ G.Π.$₁ (G.TF.com₁ (G.TF.bwd ρ) {a₀}, G.idnˢ A S.Π.$₀ T.𝟙.*) )

    .pnt
      : ∀ {a₀ a₁ a₂ a₃ : G.obj A}
      → S.homᵗ (G.homˢ A _)
        ( G.cmpˢ A S.Π.$₀
          ( G.TF.com₁ (G.TF.fwd α) {(a₀ , a₁) , ⊗ G.Π.$₀ (a₂ , a₃)}
          , G.TF.com₁ (G.TF.fwd α) {(⊗ G.Π.$₀ (a₀ , a₁) , a₂) , a₃} )
        , G.cmpˢ A S.Π.$₀
          ( ⊗ G.Π.$₁
            ( G.idnˢ A S.Π.$₀ T.𝟙.*
            , G.TF.com₁ (G.TF.fwd α) {(a₁ , a₂) , a₃} )
          , G.cmpˢ A S.Π.$₀
            ( G.TF.com₁ (G.TF.fwd α) {(a₀ , ⊗ G.Π.$₀ (a₁ , a₂)) , a₃}
            , ⊗ G.Π.$₁
              ( G.TF.com₁ (G.TF.fwd α) {(a₀ , a₁) , a₂}
              , G.idnˢ A S.Π.$₀ T.𝟙.* ) ) ) )
