{-# OPTIONS --without-K #-}

module Groupoid.Iso where

open import Agda.Primitive
open import Common
import Groupoid.Core.Base as G
import Setoid as S
open import Type as T
  using (_,_)

record t
  {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  {A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ}
  (a₀ a₁ : G.obj A)
    : Set (ℓˢᵒ ⊔ ℓˢʰ)
  where
    field
      fwd : S.obj (G.homˢ A (a₀ , a₁))
      bwd : S.obj (G.homˢ A (a₁ , a₀))
    field
      .iso-fwd :
          S.homᵗ (G.homˢ A (a₀ , a₀))
            ( G.cmpˢ A S.Π.$₀ (bwd , fwd)
            , G.idnˢ A S.Π.$₀ T.𝟙.* )
      .iso-bwd :
          S.homᵗ (G.homˢ A (a₁ , a₁))
            ( G.cmpˢ A S.Π.$₀ (fwd , bwd)
            , G.idnˢ A S.Π.$₀ T.𝟙.* )
open t

s : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ}
  → (a₀ a₁ : G.obj A)
  → S.t Dir.≈ _ _
S.obj (s {A = A} a₀ a₁) =
  t {A = A} a₀ a₁
S.homᵗ (s {A = A} _ _) (f , g) =
  G.hom₁ A (fwd f) (fwd g)
S.idnᵗ (s {A = A} _ _) =
  S.idnᵗ (G.homˢ A _)
S.cmpᵗ (s {A = A} _ _) =
  S.cmpᵗ (G.homˢ A _)
S.invᵗ (s {A = A} _ _) =
  S.invᵗ (G.homˢ A _)

g : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → (A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ)
  → G.t d _ _ _
G.obj (g A) =
  G.obj A
G.homˢ (g A) (a , b) =
  s {A = A} a b

fwd (S.Π._$₀_ (G.idnˢ (g A) {a}) _) =
  G.idn₀ A
bwd (S.Π._$₀_ (G.idnˢ (g A) {a}) _) =
  G.idn₀ A
iso-fwd (S.Π._$₀_ (G.idnˢ (g A)) _) =
  G.idn-lhs A _
iso-bwd (S.Π._$₀_ (G.idnˢ (g A)) _) =
  G.idn-lhs A _

S.Π._$₁_ (G.idnˢ (g A)) _ =
  S.idnᵗ (G.homˢ A _) _

fwd (S.Π._$₀_ (G.cmpˢ (g A)) (g , f)) =
  G.cmp₀ A (fwd g) (fwd f)
bwd (S.Π._$₀_ (G.cmpˢ (g A)) (g , f)) =
  G.cmp₀ A (bwd f) (bwd g)
iso-fwd (S.Π._$₀_ (G.cmpˢ (g A)) (g , f)) =
  S.cmpᵗ (G.homˢ A _)
    ( S.cmpᵗ (G.homˢ A _)
      ( iso-fwd f
      , G.cmpˢ A S.Π.$₁
        ( S.idnᵗ (G.homˢ A _) _
        , S.cmpᵗ (G.homˢ A _)
          ( S.cmpᵗ (G.homˢ A _)
            ( G.idn-lhs A _
            , G.cmpˢ A S.Π.$₁
              ( iso-fwd g
              , S.idnᵗ (G.homˢ A _) _ ) )
          , S.invᵗ (G.homˢ A _) (G.cmp-ass A _ _ _) ) ) )
    , G.cmp-ass A _ _ _ )
iso-bwd (S.Π._$₀_ (G.cmpˢ (g A)) (g , f)) =
  S.cmpᵗ (G.homˢ A _)
    ( S.cmpᵗ (G.homˢ A _)
      ( iso-bwd g
      , G.cmpˢ A S.Π.$₁
        ( S.idnᵗ (G.homˢ A _) _
        , S.cmpᵗ (G.homˢ A _)
          ( S.cmpᵗ (G.homˢ A _)
            ( G.idn-lhs A _
            , G.cmpˢ A S.Π.$₁
              ( iso-bwd f
              , S.idnᵗ (G.homˢ A _) _ ) )
          , S.invᵗ (G.homˢ A _) (G.cmp-ass A _ _ _) ) ) )
    , G.cmp-ass A _ _ _ )
S.Π._$₁_ (G.cmpˢ (g A)) {g₀ , f₀}{g₁ , f₁} =
  G.cmpˢ A S.Π.$₁_

G.invˢ (g {Dir.≤} A) =
  _
fwd (S.Π._$₀_ (G.invˢ (g {Dir.≈} A)) f) =
  G.inv₀ A (fwd f)
bwd (S.Π._$₀_ (G.invˢ (g {Dir.≈} A)) f) =
  G.inv₀ A (bwd f)
iso-fwd (S.Π._$₀_ (G.invˢ (g {Dir.≈} A)) f) =
  S.cmpᵗ (G.homˢ A _)
    ( iso-bwd f
    , G.cmpˢ A S.Π.$₁
      ( S.cmpᵗ (G.homˢ A _)
        ( S.cmpᵗ (G.homˢ A _)
          ( S.cmpᵗ (G.homˢ A _)
            ( G.idn-lhs A _
            , G.cmpˢ A S.Π.$₁
              ( G.inv-lhs A _
              , S.idnᵗ (G.homˢ A _) _ ) )
          , S.invᵗ (G.homˢ A _) (G.cmp-ass A _ _ _) )
        , S.cmpᵗ (G.homˢ A _)
          ( G.cmpˢ A S.Π.$₁
            ( S.idnᵗ (G.homˢ A _) _
            , S.invᵗ (G.homˢ A _) (iso-fwd f) )
          , G.idn-rhs A _ ) )
      , S.cmpᵗ (G.homˢ A _)
        ( S.cmpᵗ (G.homˢ A _)
          ( S.cmpᵗ (G.homˢ A _)
            ( S.invᵗ (G.homˢ A _) (G.idn-rhs A _)
            , G.cmpˢ A S.Π.$₁
              ( S.idnᵗ (G.homˢ A _) _
              , S.invᵗ (G.homˢ A _) (G.inv-rhs A _) ) )
          , G.cmp-ass A _ _ _ )
        , S.cmpᵗ (G.homˢ A _)
          ( G.cmpˢ A S.Π.$₁
            ( S.invᵗ (G.homˢ A _) (iso-fwd f)
            , S.idnᵗ (G.homˢ A _) _ )
          , S.invᵗ (G.homˢ A _) (G.idn-lhs A _) ) ) ) )
iso-bwd (S.Π._$₀_ (G.invˢ (g {Dir.≈} A)) f) =
  S.cmpᵗ (G.homˢ A _)
    ( iso-fwd f
    , G.cmpˢ A S.Π.$₁
      ( S.cmpᵗ (G.homˢ A _)
        ( S.cmpᵗ (G.homˢ A _)
          ( S.cmpᵗ (G.homˢ A _)
            ( G.idn-lhs A _
            , G.cmpˢ A S.Π.$₁
              ( G.inv-lhs A _
              , S.idnᵗ (G.homˢ A _) _ ) )
          , S.invᵗ (G.homˢ A _) (G.cmp-ass A _ _ _) )
        , S.cmpᵗ (G.homˢ A _)
          ( G.cmpˢ A S.Π.$₁
            ( S.idnᵗ (G.homˢ A _) _
            , S.invᵗ (G.homˢ A _) (iso-bwd f) )
          , G.idn-rhs A _ ) )
      , S.cmpᵗ (G.homˢ A _)
        ( S.cmpᵗ (G.homˢ A _)
          ( S.cmpᵗ (G.homˢ A _)
            ( S.invᵗ (G.homˢ A _) (G.idn-rhs A _)
            , G.cmpˢ A S.Π.$₁
              ( S.idnᵗ (G.homˢ A _) _
              , S.invᵗ (G.homˢ A _) (G.inv-rhs A _) ) )
          , G.cmp-ass A _ _ _ )
        , S.cmpᵗ (G.homˢ A _)
          ( G.cmpˢ A S.Π.$₁
            ( S.invᵗ (G.homˢ A _) (iso-bwd f)
            , S.idnᵗ (G.homˢ A _) _ )
          , S.invᵗ (G.homˢ A _) (G.idn-lhs A _) ) ) ) )
S.Π._$₁_ (G.invˢ (g {Dir.≈} A)) =
  G.invˢ A S.Π.$₁_

G.idn-lhs (g A) _ =
  G.idn-lhs A _
G.idn-rhs (g A) _ =
  G.idn-rhs A _
G.cmp-ass (g A) _ _ _ =
  G.cmp-ass A _ _ _
G.inv-lhs (g {Dir.≤} A) =
  _
G.inv-lhs (g {Dir.≈} A) _ =
  G.inv-lhs A _
G.inv-rhs (g {Dir.≤} A) =
  _
G.inv-rhs (g {Dir.≈} A) _ =
  G.inv-rhs A _
