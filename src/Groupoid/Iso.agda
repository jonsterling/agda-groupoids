{-# OPTIONS --without-K #-}

module Groupoid.Iso {d} where

open import Agda.Primitive
open import Common
import Groupoid.Core.Base as G
import Setoid as S
open import Type as T
  using (_,_)

record t
  ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  {A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ}
  (a₀ a₁ : G.obj A)
    : Set (ℓˢᵒ ⊔ ℓˢʰ)
  where
    field
      fwd : S.obj (G.homˢ A (a₀ , a₁))
      bwd : S.obj (G.homˢ A (a₁ , a₀))
    field
      .{iso-fwd} :
          S.homᵗ (G.homˢ A (a₀ , a₀))
            ( G.cmpˢᵐ A S.Π.$₀ (bwd , fwd)
            , G.idnˢᵐ A S.Π.$₀ T.𝟙.* )
      .{iso-bwd} : 
          S.homᵗ (G.homˢ A (a₁ , a₁))
            ( G.cmpˢᵐ A S.Π.$₀ (fwd , bwd)
            , G.idnˢᵐ A S.Π.$₀ T.𝟙.* )
