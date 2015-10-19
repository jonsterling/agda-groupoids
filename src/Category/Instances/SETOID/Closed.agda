{-# OPTIONS --without-K #-}

module Category.Instances.SETOID.Closed where

open import Agda.Primitive
private
  module C where
    open import Category public
    module I where
      module SETOID where
        open import Category.Instances.SETOID public
private
  module G where
    open import Groupoid public
      hiding (module Map)
    module Clo where
      open import Groupoid.Closed public
        hiding (module G)
    module Map where
      open Groupoid.Map public
      open import Groupoid.Dinatural public
import Setoid as S
open import Type as T
  using (_,_)

-- SETOID is a closed category (incomplete)
clo
  : ∀ ..{ℓ}
  → G.Clo.t (C.I.SETOID.c ℓ ℓ)

-- ⊸
G.Map._$₀_ (G.Clo.t.⊸ clo) (A , B) =
  A S.Map.⇒₀ˢ B
S.Map._$₀_ (S.Map._$₀_ (G.Map.-$₁ˢ- (G.Clo.t.⊸ clo)) (f , g)) h =
  g S.Map.∘₀ h S.Map.∘₀ f
S.Map.com₁ (S.Map._$₁_ (S.Map._$₀_ (G.Map.-$₁ˢ- (G.Clo.t.⊸ clo)) (_ , g)) α) =
  g S.Map.$₁ S.Map.com₁ α
S.Map.com₁ (S.Map.com₁ (S.Map._$₁_ (G.Map.-$₁ˢ- (G.Clo.t.⊸ clo) {_}{_ , D}) {_ , g₀} (α , β)) {h}) =
  S.cmpᵗ D (S.Map.com₁ β , g₀ S.Map.$₁ h S.Map.$₁ S.Map.com₁ α)
S.Map.com₁ (S.Map.com₁ (G.Map.idn (G.Clo.t.⊸ clo) {_ , B})) =
  S.idnᵗ B _
S.Map.com₁ (S.Map.com₁ (G.Map.cmp (G.Clo.t.⊸ clo) {_}{_}{_ , R} _ _)) =
  S.idnᵗ R _

-- 𝟙
G.Clo.t.𝟙 clo =
  S.𝟙.s

-- susp
S.Map._$₀_ (G.Map.com₁ (G.Map.fwd (G.Clo.t.susp clo)) {A}) a =
  S.Map.!ˢ a
S.Map.com₁ (S.Map._$₁_ (G.Map.com₁ (G.Map.fwd (G.Clo.t.susp clo)) {A}) {a}{b} f) =
  f
S.Map.com₁ (S.Map.com₁ (G.Map.nat₁ (G.Map.fwd (G.Clo.t.susp clo)) {_}{B} f)) =
  S.idnᵗ B _
S.Map._$₀_ (G.Map.com₁ (G.Map.bwd (G.Clo.t.susp clo)) {A}) =
  S.Map._$₀ T.𝟙.*
S.Map._$₁_ (G.Map.com₁ (G.Map.bwd (G.Clo.t.susp clo)) {A}) {f₀}{f₁} α =
  S.Map.com₁ α
S.Map.com₁ (G.Map.nat₁ (G.Map.bwd (G.Clo.t.susp clo)) {_}{B} f) =
  S.idnᵗ B _
S.Map.com₁ (G.Map.com₂ (G.Map.iso-fwd (G.Clo.t.susp clo)) {A}) =
  S.idnᵗ A _
S.Map.com₁ (S.Map.com₁ (G.Map.com₂ (G.Map.iso-bwd (G.Clo.t.susp clo)) {A})) =
  S.idnᵗ A _

-- idn
S.Map._$₀_ (G.Map._:⇏₁ᵗ_.com₁ (G.Clo.t.idn clo) {A}) _ =
  S.Map.idn₀ᵗ _
S.Map.com₁ (S.Map._$₁_ (G.Map._:⇏₁ᵗ_.com₁ (G.Clo.t.idn clo) {A}) _) {a} =
  S.idnᵗ A {a} _
S.Map.com₁ (S.Map.com₁ (G.Map._:⇏₁ᵗ_.nat₁ (G.Clo.t.idn clo) {_}{B} f)) =
  S.idnᵗ B _

-- cmp
G.Clo.t.cmp clo = record
  { com₁ = λ {A} → record
    { com₁ = λ { {B , C} → record
      { _$₀_ = λ G → record
        { _$₀_ = G S.Map.∘₀_
        ; _$₁_ = λ α → S.Map.cmp₁ᵗ-w₀ (G , α)
        }
      ; _$₁_ = λ α → record
        { com₁ = λ {F} → S.Map.cmp₁ᵗ-w₁ (α , F) }
      }
    }
    ; nat₁ = λ { {C , D}{B , E} (G , K) → record
        { com₁ = λ {H} → record
          { com₁ = λ {F} → record
            { com₁ = λ {a} → S.idnᵗ E {K S.Map.$₀ H S.Map.$₀ G S.Map.$₀ F S.Map.$₀ a} _ }
          }
        }
      }
    }
  ; nat₁ = λ {A}{B} F → record
      { com₂ = λ { {C , D} → record
        { com₁ = λ {H} → record
          { com₁ = λ {G} → record
            { com₁ = λ {A} → S.idnᵗ D {H S.Map.$₀ G S.Map.$₀ F S.Map.$₀ A} _ }
          }
        }
      }
    }
  }
