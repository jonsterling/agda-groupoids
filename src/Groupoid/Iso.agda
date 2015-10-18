{-# OPTIONS --without-K #-}

module Groupoid.Iso where

open import Agda.Primitive
import Ambient.Groupoid.Base as G
import Setoid as S
open import Type as T

record t
  {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  {A : G.𝔊₂,₀ d ℓᵒ ℓˢᵒ ℓˢʰ}
  (a₀ a₁ : G.obj A)
    : Set (ℓˢᵒ ⊔ ℓˢʰ)
  where
    field
      fwd : S.cell₀ (G.homˢ A (a₀ , a₁))
      bwd : S.cell₀ (G.homˢ A (a₁ , a₀))
    field
      .iso-fwd :
          S.cell₁ (G.homˢ A (a₀ , a₀))
            ( G.cmpˢ A S.Map.$₀ (bwd , fwd)
            , G.idnˢ A S.Map.$₀ * )
      .iso-bwd :
          S.cell₁ (G.homˢ A (a₁ , a₁))
            ( G.cmpˢ A S.Map.$₀ (fwd , bwd)
            , G.idnˢ A S.Map.$₀ * )
open t

s : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.𝔊₂,₀ d ℓᵒ ℓˢᵒ ℓˢʰ}
  → (a₀ a₁ : G.obj A)
  → S.𝔊₁ G.Dir.≈ _ _
S.cell₀ (s {A = A} a₀ a₁) =
  t {A = A} a₀ a₁
S.cell₁ (s {A = A} _ _) (f , g) =
  G.hom₁ A (fwd f) (fwd g)
S.idn (s {A = A} _ _) =
  S.idn (G.homˢ A _)
S.cmp (s {A = A} _ _) =
  S.cmp (G.homˢ A _)
S.inv (s {A = A} _ _) =
  S.inv (G.homˢ A _)

g : ∀ {d′} d ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → (A : G.𝔊₂,₀ d′ ℓᵒ ℓˢᵒ ℓˢʰ)
  → G.𝔊₂,₀ d _ _ _
G.obj (g d A) =
  G.obj A
G.homˢ (g d A) (a , b) =
  s {A = A} a b

-- idn
fwd (S.Map._$₀_ (G.idnˢ (g d A) {a}) _) =
  G.idn₀ A
bwd (S.Map._$₀_ (G.idnˢ (g d A) {a}) _) =
  G.idn₀ A
iso-fwd (S.Map._$₀_ (G.idnˢ (g d A)) _) =
  G.idn-lhs A _
iso-bwd (S.Map._$₀_ (G.idnˢ (g d A)) _) =
  G.idn-lhs A _
S.Map._$₁_ (G.idnˢ (g d A)) _ =
  S.idn (G.homˢ A _) _

-- cmp
fwd (S.Map._$₀_ (G.cmpˢ (g d A)) (g , f)) =
  G.cmp₀ A (fwd g) (fwd f)
bwd (S.Map._$₀_ (G.cmpˢ (g d A)) (g , f)) =
  G.cmp₀ A (bwd f) (bwd g)
iso-fwd (S.Map._$₀_ (G.cmpˢ (g d A)) (g , f)) =
  S.cmp (G.homˢ A _)
    ( S.cmp (G.homˢ A _)
      ( iso-fwd f
      , G.cmpˢ A S.Map.$₁
        ( S.idn (G.homˢ A _) _
        , S.cmp (G.homˢ A _)
          ( S.cmp (G.homˢ A _)
            ( G.idn-lhs A _
            , G.cmpˢ A S.Map.$₁
              ( iso-fwd g
              , S.idn (G.homˢ A _) _ ) )
          , S.inv (G.homˢ A _) (G.cmp-ass A _ _ _) ) ) )
    , G.cmp-ass A _ _ _ )
iso-bwd (S.Map._$₀_ (G.cmpˢ (g d A)) (g , f)) =
  S.cmp (G.homˢ A _)
    ( S.cmp (G.homˢ A _)
      ( iso-bwd g
      , G.cmpˢ A S.Map.$₁
        ( S.idn (G.homˢ A _) _
        , S.cmp (G.homˢ A _)
          ( S.cmp (G.homˢ A _)
            ( G.idn-lhs A _
            , G.cmpˢ A S.Map.$₁
              ( iso-bwd f
              , S.idn (G.homˢ A _) _ ) )
          , S.inv (G.homˢ A _) (G.cmp-ass A _ _ _) ) ) )
    , G.cmp-ass A _ _ _ )
S.Map._$₁_ (G.cmpˢ (g d A)) {g₀ , f₀}{g₁ , f₁} =
  G.cmpˢ A S.Map.$₁_

-- inv
G.invˢ (g G.Dir.≤ A) =
  _
fwd (S.Map._$₀_ (G.invˢ (g G.Dir.≈ A)) f) =
  bwd f
bwd (S.Map._$₀_ (G.invˢ (g G.Dir.≈ A)) f) =
  fwd f
iso-fwd (S.Map._$₀_ (G.invˢ (g G.Dir.≈ A)) f) =
  iso-bwd f
iso-bwd (S.Map._$₀_ (G.invˢ (g G.Dir.≈ A)) f) =
  iso-fwd f
S.Map._$₁_ (G.invˢ (g G.Dir.≈ A)) {f₀}{f₁} p =
  S.cmp (G.homˢ A _)
    ( S.cmp (G.homˢ A _)
      ( S.cmp (G.homˢ A _)
        ( S.cmp (G.homˢ A _)
          ( G.idn-lhs A _
          , G.cmpˢ A S.Map.$₁
              ( S.cmp (G.homˢ A _)
                ( iso-fwd f₀
                , G.cmpˢ A S.Map.$₁
                  ( S.idn (G.homˢ A _) _
                  , S.inv (G.homˢ A _) p ) )
              , S.idn (G.homˢ A _) _) )
        , S.inv (G.homˢ A _) (G.cmp-ass A _ _ _) )
      , G.cmpˢ A S.Map.$₁
        ( S.idn (G.homˢ A _) _
        , S.inv (G.homˢ A _) (iso-bwd f₁) ) )
    , S.inv (G.homˢ A _) (G.idn-rhs A _) )

G.idn-lhs (g d A) _ =
  G.idn-lhs A _
G.idn-rhs (g d A) _ =
  G.idn-rhs A _
G.cmp-ass (g d A) _ _ _ =
  G.cmp-ass A _ _ _
G.inv-lhs (g G.Dir.≤ A) =
  _
G.inv-lhs (g G.Dir.≈ A) f =
  iso-fwd f
G.inv-rhs (g G.Dir.≤ A) =
  _
G.inv-rhs (g G.Dir.≈ A) f =
  S.inv (G.homˢ A _) (iso-bwd f)
