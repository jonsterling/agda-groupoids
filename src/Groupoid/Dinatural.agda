{-# OPTIONS --without-K #-}

open import Common
module Groupoid.Dinatural {d : Dir.t} where

open import Agda.Primitive
private
  module G where
    open import Groupoid public
      hiding (module Map)
    module Map where
      open Groupoid.Map public
      open import Groupoid.Profunctor public
import Setoid as S
open import Type as T
  using (_,_)

infixr 0 _:⇏₁ᵗ_

record _:⇏₁ᵗ_
  ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  {A : G.𝔊₂,₀ d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  {B : G.𝔊₂,₀ d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  (F G : (G.Op.g A G.Ten.⊗ A) G.Map.⇒₀ᵗ B)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ˢᵒ) ⊔ (ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  field
    com₁
      : ∀ {a}
      → S.cell₀ (G.homˢ B (F G.Map.$₀ (a , a) , G G.Map.$₀ (a , a)))
  field
    .nat₁
      : ∀ {a b}
      → (f : S.cell₀ (G.homˢ A (a , b)))
      → S.cell₁ (G.homˢ B (F G.Map.$₀ (b , a) , G G.Map.$₀ (a , b)))
          ( G.cmpˢ B S.Map.$₀
            ( G G.Map.$₁ (G.idnˢ (G.Op.g A) S.Map.$₀ _ , f)
            , G.cmpˢ B S.Map.$₀
              ( com₁ {a}
              , F G.Map.$₁ (f , G.idnˢ A S.Map.$₀ _) ) )
          , G.cmpˢ B S.Map.$₀
            ( G G.Map.$₁ (f , G.idnˢ A S.Map.$₀ _)
            , G.cmpˢ B S.Map.$₀
              ( com₁ {b}
              , F G.Map.$₁ (G.idnˢ (G.Op.g A) S.Map.$₀ _ , f) ) ) )

_:Δ⇏₁ᵗ_
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.𝔊₂,₀ d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {V : G.𝔊₂,₀ d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (d : G.obj V)
  → (P : A G.Map.:[ V ]⇏₀ᵗ A)
  → Set _
_:Δ⇏₁ᵗ_ {V = V} d P = G.Map.!:[ V ]₀ d :⇏₁ᵗ P

_:⇏∇₁ᵗ_
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.𝔊₂,₀ d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {V : G.𝔊₂,₀ d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (P : A G.Map.:[ V ]⇏₀ᵗ A)
  → (d : G.obj V)
  → Set _
_:⇏∇₁ᵗ_ {V = V} P d = P :⇏₁ᵗ G.Map.!:[ V ]₀ d
