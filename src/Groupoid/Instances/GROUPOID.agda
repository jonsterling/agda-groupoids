{-# OPTIONS --without-K #-}

module Groupoid.Instances.GROUPOID where

open import Agda.Primitive
open import Common
private
  module G where
    open import Groupoid public
    module ≅ where
      open import Groupoid.Iso public
import Setoid as S
open import Type as T
  using (_,_)

c : ∀ d ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) → G.t Dir.≤ _ _ _
-- obj
G.obj (c d ℓᵒ ℓˢᵒ ℓˢʰ) =
  G.t d ℓᵒ ℓˢᵒ ℓˢʰ
-- hom
G.homˢ (c _ _ _ _) (a , b) =
  G.s (G.≅.g Dir.≈ (a G.Π.⇒₀ᵍ b))
-- idn
S.Π._$₀_ (G.idnˢ (c _ _ _ _)) =
  G.Π.idn₀ᵗ
S.Π._$₁_ (G.idnˢ (c _ _ _ _)) _ =
  G.idnˢ (G.≅.g Dir.≈ _) S.Π.$₀ _
-- cmp
S.Π._$₀_ (G.cmpˢ (c _ _ _ _)) =
  G.Π.cmp₀ᵗ
G.≅.t.fwd (S.Π._$₁_ (G.cmpˢ (c _ _ _ _)) (p , q)) =
  G.TF.cmp₀ˢ-h₀ S.Π.$₀ (G.≅.t.fwd p , G.≅.t.fwd q)
G.≅.t.bwd (S.Π._$₁_ (G.cmpˢ (c _ _ _ _)) (p , q)) =
  G.TF.cmp₀ˢ-h₀ S.Π.$₀ (G.≅.t.bwd p , G.≅.t.bwd q)
G.TF.com₂ (G.≅.t.iso-fwd (S.Π._$₁_ (G.cmpˢ (c _ _ _ _) {_}{_}{C}) {g₀ , _} (p , q))) =
  S.cmpᵗ (G.homˢ C _)
    ( S.cmpᵗ (G.homˢ C _)
      ( S.cmpᵗ (G.homˢ C _)
        ( S.cmpᵗ (G.homˢ C _)
          ( S.cmpᵗ (G.homˢ C _)
            ( S.cmpᵗ (G.homˢ C _)
              ( G.Π.idn g₀
              , g₀ G.Π.$₂ G.TF.com₂ (G.≅.t.iso-fwd q) )
            , S.invᵗ (G.homˢ C _) (G.Π.cmp g₀ _ _) )
          , G.cmpˢ C S.Π.$₁
            ( S.idnᵗ (G.homˢ C _) _
            , S.cmpᵗ (G.homˢ C _)
              ( G.idn-lhs C _
              , G.cmpˢ C S.Π.$₁
                ( G.TF.com₂ (G.≅.t.iso-fwd p)
                , S.idnᵗ (G.homˢ C _) _) ) ) )
        , G.cmpˢ C S.Π.$₁
          ( S.idnᵗ (G.homˢ C _) _
          , S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _) ) )
      , G.cmp-ass C _ _ _ )
    , G.cmpˢ C S.Π.$₁
      ( S.idnᵗ (G.homˢ C _) _
      , S.invᵗ (G.homˢ C _) (G.TF.nat₁ (G.≅.t.fwd p) (G.TF.com₁ (G.≅.t.fwd q))) ) )
G.TF.com₂ (G.≅.t.iso-bwd (S.Π._$₁_ (G.cmpˢ (c _ _ _ _) {_}{_}{C}) {_ , _}{g₁ , _} (p , q))) =
  S.cmpᵗ (G.homˢ C _)
    ( S.cmpᵗ (G.homˢ C _)
      ( S.cmpᵗ (G.homˢ C _)
        ( S.cmpᵗ (G.homˢ C _)
          ( S.cmpᵗ (G.homˢ C _)
            ( S.cmpᵗ (G.homˢ C _)
              ( G.Π.idn g₁
              , g₁ G.Π.$₂ G.TF.com₂ (G.≅.t.iso-bwd q) )
            , S.invᵗ (G.homˢ C _) (G.Π.cmp g₁ _ _) )
          , G.cmpˢ C S.Π.$₁
            ( S.idnᵗ (G.homˢ C _) _
            , S.cmpᵗ (G.homˢ C _)
              ( G.idn-lhs C _
              , G.cmpˢ C S.Π.$₁
                ( G.TF.com₂ (G.≅.t.iso-bwd p)
                , S.idnᵗ (G.homˢ C _) _) ) ) )
        , G.cmpˢ C S.Π.$₁
          ( S.idnᵗ (G.homˢ C _) _
          , S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _) ) )
      , G.cmp-ass C _ _ _ )
    , G.cmpˢ C S.Π.$₁
      ( S.idnᵗ (G.homˢ C _) _
      , S.invᵗ (G.homˢ C _) (G.TF.nat₁ (G.≅.t.bwd p) (G.TF.com₁ (G.≅.t.bwd q))) ) )

-- inv
G.invˢ (c d ℓᵒ ℓˢᵒ ℓˢʰ) =
  _

-- laws
G.TF.com₁ (G.≅.t.fwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) =
  G.idnˢ B S.Π.$₀ _
G.TF.nat₁ (G.≅.t.fwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) _ =
  S.cmpᵗ (G.homˢ B _)
    ( G.idn-rhs B _
    , G.idn-lhs B _ )
G.TF.com₁ (G.≅.t.bwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) =
  G.idnˢ B S.Π.$₀ _
G.TF.nat₁ (G.≅.t.bwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) _ =
  S.cmpᵗ (G.homˢ B _)
    ( G.idn-rhs B _
    , G.idn-lhs B _ )
G.TF.com₂ (G.≅.t.iso-fwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) =
  G.idn-lhs B (G.idnˢ B S.Π.$₀ T.𝟙.*)
G.TF.com₂ (G.≅.t.iso-bwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) =
  G.idn-lhs B (G.idnˢ B S.Π.$₀ T.𝟙.*)

G.TF.com₁ (G.≅.t.fwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) =
  G.idnˢ B S.Π.$₀ _
G.TF.nat₁ (G.≅.t.fwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) _ =
  S.cmpᵗ (G.homˢ B _)
    ( G.idn-rhs B _
    , G.idn-lhs B _ )
G.TF.com₁ (G.≅.t.bwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) =
  G.idnˢ B S.Π.$₀ _
G.TF.nat₁ (G.≅.t.bwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) _ =
  S.cmpᵗ (G.homˢ B _)
    ( G.idn-rhs B _
    , G.idn-lhs B _ )
G.TF.com₂ (G.≅.t.iso-fwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) =
  G.idn-lhs B (G.idnˢ B S.Π.$₀ T.𝟙.*)
G.TF.com₂ (G.≅.t.iso-bwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) {a} =
  G.idn-lhs B (G.idnˢ B S.Π.$₀ T.𝟙.*)
  -- G.idn-lhs B _

G.TF.com₁ (G.≅.t.fwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) =
  G.idnˢ D S.Π.$₀ _
G.TF.nat₁ (G.≅.t.fwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) _ =
  S.cmpᵗ (G.homˢ D _)
    ( G.idn-rhs D _
    , G.idn-lhs D _ )
G.TF.com₁ (G.≅.t.bwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) =
  G.idnˢ D S.Π.$₀ _
G.TF.nat₁ (G.≅.t.bwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) _ =
  S.cmpᵗ (G.homˢ D _)
    ( G.idn-rhs D _
    , G.idn-lhs D _ )
G.TF.com₂ (G.≅.t.iso-fwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) =
  G.idn-lhs D (G.idnˢ D S.Π.$₀ T.𝟙.*)
G.TF.com₂ (G.≅.t.iso-bwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) =
  G.idn-lhs D (G.idnˢ D S.Π.$₀ T.𝟙.*)
  -- G.idn-lhs D _

G.inv-lhs (c _ _ _ _) =
  _
G.inv-rhs (c _ _ _ _) =
  _

g : ∀ d ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) → G.t d _ _ _
g d ℓᵒ ℓˢᵒ ℓˢʰ = G.≅.g d (c d ℓᵒ ℓˢᵒ ℓˢʰ)
