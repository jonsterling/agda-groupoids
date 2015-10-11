{-# OPTIONS --without-K #-}

module Groupoid.Closed where

open import Agda.Primitive
module G where
  open import Groupoid public
    hiding (module Π; module TF)
  module Π where
    open Groupoid.Π public
    open import Groupoid.Bifunctor public
    open import Groupoid.Presheaf public
    open import Groupoid.Profunctor public
  module TF where
    open Groupoid.TF public
    open import Groupoid.Dinatural public
import Setoid as S
open import Type as T
  using (_,_)

record t {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  (A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ)
    : Set (ℓᵒ ⊔ ℓˢᵒ ⊔ ℓˢʰ) where
  no-eta-equality
  field
    ⊸ : A G.Π.:[ A ]⇏₀ᵗ A
    𝟙 : G.obj A

  lazy : A G.Π.⇒₀ᵗ A
  lazy = ⊸ G.Π.:⟨ 𝟙 ,-⟩

  dual : A G.Π.⇏₀ᵗ A
  dual = ⊸ G.Π.:⟨-, 𝟙 ⟩

  field
    susp : G.Π.idn₀ᵗ T.𝟙.* G.TF.≅ lazy
    idn : G.Π.!:[ A ]₀ 𝟙 G.TF.:⇏₁ᵗ ⊸
