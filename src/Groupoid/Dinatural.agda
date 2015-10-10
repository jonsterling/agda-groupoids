{-# OPTIONS --without-K #-}

open import Common
module Groupoid.Dinatural {d : Dir.t} where

open import Agda.Primitive
import Groupoid as G
import Setoid as S
open import Type as T
  using (_,_)

infixr 0 _:⇏₁ᵗ_

record _:⇏₁ᵗ_
  ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  (F G : (G.Op.g A G.∐.⊗ A) G.Π.⇒₀ᵗ B)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ˢᵒ) ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  field
    com₁
      : ∀ {a}
      → S.obj (G.homˢ B (F G.Π.$₀ (a , a) , G G.Π.$₀ (a , a)))
  field
    .nat₁
      : ∀ {a b}
      → (f : S.obj (G.homˢ A (a , b)))
      → S.homᵗ (G.homˢ B (F G.Π.$₀ (b , a) , G G.Π.$₀ (a , b)))
          ( G.cmpˢ B S.Π.$₀
            ( G G.Π.$₁ (G.idnˢ (G.Op.g A) S.Π.$₀ _ , f)
            , G.cmpˢ B S.Π.$₀
              ( com₁ {a}
              , F G.Π.$₁ (f , G.idnˢ A S.Π.$₀ _) ) )
          , G.cmpˢ B S.Π.$₀
            ( G G.Π.$₁ (f , G.idnˢ A S.Π.$₀ _)
            , G.cmpˢ B S.Π.$₀
              ( com₁ {b}
              , F G.Π.$₁ (G.idnˢ (G.Op.g A) S.Π.$₀ _ , f) ) ) )
open _:⇏₁ᵗ_ public
