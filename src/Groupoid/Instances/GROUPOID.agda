{-# OPTIONS --without-K #-}

module Groupoid.Instances.GROUPOID where

open import Agda.Primitive
private
  module G where
    open import Groupoid public
    module ≅ where
      open import Groupoid.Iso public
import Setoid as S
open import Type as T
  using (_,_)

c : ∀ d ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) → G.t G.Dir.≤ _ _ _
-- obj
G.obj (c d ℓᵒ ℓˢᵒ ℓˢʰ) =
  G.t d ℓᵒ ℓˢᵒ ℓˢʰ
-- hom
G.homˢ (c _ _ _ _) (a , b) =
  G.G↓S (G.≅.g G.Dir.≈ (a G.Map.⇒₀ᵍ b))
-- idn
S.Map._$₀_ (G.idnˢ (c _ _ _ _)) =
  G.Map.idn₀ᵗ
S.Map._$₁_ (G.idnˢ (c _ _ _ _)) _ =
  G.idnˢ (G.≅.g G.Dir.≈ _) S.Map.$₀ _
-- cmp
S.Map._$₀_ (G.cmpˢ (c _ _ _ _)) =
  G.Map.cmp₀ᵗ
G.≅.t.fwd (S.Map._$₁_ (G.cmpˢ (c _ _ _ _)) (p , q)) =
  G.Map.cmp₀ˢ-h₀ S.Map.$₀ (G.≅.t.fwd p , G.≅.t.fwd q)
G.≅.t.bwd (S.Map._$₁_ (G.cmpˢ (c _ _ _ _)) (p , q)) =
  G.Map.cmp₀ˢ-h₀ S.Map.$₀ (G.≅.t.bwd p , G.≅.t.bwd q)
G.Map.com₂ (G.≅.t.iso-fwd (S.Map._$₁_ (G.cmpˢ (c _ _ _ _) {_}{_}{C}) {g₀ , _} (p , q))) =
  S.cmpᵗ (G.homˢ C _)
    ( S.cmpᵗ (G.homˢ C _)
      ( S.cmpᵗ (G.homˢ C _)
        ( S.cmpᵗ (G.homˢ C _)
          ( S.cmpᵗ (G.homˢ C _)
            ( S.cmpᵗ (G.homˢ C _)
              ( G.Map.idn g₀
              , g₀ G.Map.$₂ G.Map.com₂ (G.≅.t.iso-fwd q) )
            , S.invᵗ (G.homˢ C _) (G.Map.cmp g₀ _ _) )
          , G.cmpˢ C S.Map.$₁
            ( S.idnᵗ (G.homˢ C _) _
            , S.cmpᵗ (G.homˢ C _)
              ( G.idn-lhs C _
              , G.cmpˢ C S.Map.$₁
                ( G.Map.com₂ (G.≅.t.iso-fwd p)
                , S.idnᵗ (G.homˢ C _) _) ) ) )
        , G.cmpˢ C S.Map.$₁
          ( S.idnᵗ (G.homˢ C _) _
          , S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _) ) )
      , G.cmp-ass C _ _ _ )
    , G.cmpˢ C S.Map.$₁
      ( S.idnᵗ (G.homˢ C _) _
      , S.invᵗ (G.homˢ C _) (G.Map.nat₁ (G.≅.t.fwd p) (G.Map.com₁ (G.≅.t.fwd q))) ) )
G.Map.com₂ (G.≅.t.iso-bwd (S.Map._$₁_ (G.cmpˢ (c _ _ _ _) {_}{_}{C}) {_ , _}{g₁ , _} (p , q))) =
  S.cmpᵗ (G.homˢ C _)
    ( S.cmpᵗ (G.homˢ C _)
      ( S.cmpᵗ (G.homˢ C _)
        ( S.cmpᵗ (G.homˢ C _)
          ( S.cmpᵗ (G.homˢ C _)
            ( S.cmpᵗ (G.homˢ C _)
              ( G.Map.idn g₁
              , g₁ G.Map.$₂ G.Map.com₂ (G.≅.t.iso-bwd q) )
            , S.invᵗ (G.homˢ C _) (G.Map.cmp g₁ _ _) )
          , G.cmpˢ C S.Map.$₁
            ( S.idnᵗ (G.homˢ C _) _
            , S.cmpᵗ (G.homˢ C _)
              ( G.idn-lhs C _
              , G.cmpˢ C S.Map.$₁
                ( G.Map.com₂ (G.≅.t.iso-bwd p)
                , S.idnᵗ (G.homˢ C _) _) ) ) )
        , G.cmpˢ C S.Map.$₁
          ( S.idnᵗ (G.homˢ C _) _
          , S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _) ) )
      , G.cmp-ass C _ _ _ )
    , G.cmpˢ C S.Map.$₁
      ( S.idnᵗ (G.homˢ C _) _
      , S.invᵗ (G.homˢ C _) (G.Map.nat₁ (G.≅.t.bwd p) (G.Map.com₁ (G.≅.t.bwd q))) ) )

-- inv
G.invˢ (c d ℓᵒ ℓˢᵒ ℓˢʰ) =
  _

-- laws
G.Map.com₁ (G.≅.t.fwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) =
  G.idnˢ B S.Map.$₀ _
G.Map.nat₁ (G.≅.t.fwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) _ =
  S.cmpᵗ (G.homˢ B _)
    ( S.invᵗ (G.homˢ B _) (G.idn-rhs B _)
    , G.idn-lhs B _ )
G.Map.com₁ (G.≅.t.bwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) =
  G.idnˢ B S.Map.$₀ _
G.Map.nat₁ (G.≅.t.bwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) _ =
  S.cmpᵗ (G.homˢ B _)
    ( S.invᵗ (G.homˢ B _) (G.idn-rhs B _)
    , G.idn-lhs B _ )
G.Map.com₂ (G.≅.t.iso-fwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) =
  G.idn-lhs B (G.idnˢ B S.Map.$₀ T.𝟙.*)
G.Map.com₂ (G.≅.t.iso-bwd (G.idn-lhs (c _ _ _ _) {_}{B} F)) =
  G.idn-lhs B (G.idnˢ B S.Map.$₀ T.𝟙.*)

G.Map.com₁ (G.≅.t.fwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) =
  G.idnˢ B S.Map.$₀ _
G.Map.nat₁ (G.≅.t.fwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) _ =
  S.cmpᵗ (G.homˢ B _)
    ( S.invᵗ (G.homˢ B _) (G.idn-rhs B _)
    , G.idn-lhs B _ )
G.Map.com₁ (G.≅.t.bwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) =
  G.idnˢ B S.Map.$₀ _
G.Map.nat₁ (G.≅.t.bwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) _ =
  S.cmpᵗ (G.homˢ B _)
    ( S.invᵗ (G.homˢ B _) (G.idn-rhs B _)
    , G.idn-lhs B _ )
G.Map.com₂ (G.≅.t.iso-fwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) =
  G.idn-lhs B (G.idnˢ B S.Map.$₀ T.𝟙.*)
G.Map.com₂ (G.≅.t.iso-bwd (G.idn-rhs (c _ _ _ _) {_}{B} F)) {a} =
  G.idn-lhs B (G.idnˢ B S.Map.$₀ T.𝟙.*)
  -- G.idn-lhs B _

G.Map.com₁ (G.≅.t.fwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) =
  G.idnˢ D S.Map.$₀ _
G.Map.nat₁ (G.≅.t.fwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) _ =
  S.cmpᵗ (G.homˢ D _)
    ( S.invᵗ (G.homˢ D _) (G.idn-rhs D _)
    , G.idn-lhs D _ )
G.Map.com₁ (G.≅.t.bwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) =
  G.idnˢ D S.Map.$₀ _
G.Map.nat₁ (G.≅.t.bwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) _ =
  S.cmpᵗ (G.homˢ D _)
    ( S.invᵗ (G.homˢ D _) (G.idn-rhs D _)
    , G.idn-lhs D _ )
G.Map.com₂ (G.≅.t.iso-fwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) =
  G.idn-lhs D (G.idnˢ D S.Map.$₀ T.𝟙.*)
G.Map.com₂ (G.≅.t.iso-bwd (G.cmp-ass (c _ _ _ _) {_}{_}{_}{D} _ _ _)) =
  G.idn-lhs D (G.idnˢ D S.Map.$₀ T.𝟙.*)
  -- G.idn-lhs D _

G.inv-lhs (c _ _ _ _) =
  _
G.inv-rhs (c _ _ _ _) =
  _

g : ∀ d ..(ℓᵒ ℓˢᵒ ℓˢʰ : _) → G.t d _ _ _
g d ℓᵒ ℓˢᵒ ℓˢʰ = G.≅.g d (c d ℓᵒ ℓˢᵒ ℓˢʰ)
