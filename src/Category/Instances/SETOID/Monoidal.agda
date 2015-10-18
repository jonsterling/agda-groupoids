{-# OPTIONS --without-K #-}

module Category.Instances.SETOID.Monoidal where

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
    module Mon where
      open import Groupoid.Monoidal public
import Setoid as S
open import Type as T
  using (_,_)

-- SETOID is a monoidal category
mon
  : ∀ ..{ℓᵒ ℓʰ}
  → G.Mon.t (C.I.SETOID.c ℓᵒ ℓʰ)

-- ⊗
C.Map._$₀_ (G.Mon.t.⊗ mon) (A , B) =
  A S.Ten.⊗ B
S.Map._$₀_ (S.Map._$₀_ (C.Map.-$₁ˢ- (G.Mon.t.⊗ mon)) (f₀ , f₁)) (x , y) =
  (f₀ S.Map.$₀ x) , (f₁ S.Map.$₀ y)
S.Map._$₁_ (S.Map._$₀_ (C.Map.-$₁ˢ- (G.Mon.t.⊗ mon)) (f₀ , f₁)) (p , q) =
  (f₀ S.Map.$₁ p) , (f₁ S.Map.$₁ q)
S.Map.com₁ (S.Map._$₁_ (C.Map.-$₁ˢ- (G.Mon.t.⊗ mon)) (p , q))
  = S.Map.com₁ p
  , S.Map.com₁ q
S.Map.com₁ (C.Map.idn (G.Mon.t.⊗ mon) {A , B})
  = S.idn A _
  , S.idn B _
S.Map.com₁ (C.Map.cmp (G.Mon.t.⊗ mon) {_}{_}{A , B} _ _)
  = S.idn A _
  , S.idn B _

-- 𝟙
G.Mon.t.𝟙 mon =
  S.𝟙.s

-- λ
S.Map._$₀_ (C.Map.com₁ (C.Map.fwd (G.Mon.t.ƛ mon))) (_ , a) =
  a
S.Map._$₁_ (C.Map.com₁ (C.Map.fwd (G.Mon.t.ƛ mon))) (_ , f) =
  f
S.Map.com₁ (C.Map.nat₁ (C.Map.fwd (G.Mon.t.ƛ mon)) {_}{A} _) =
  S.idn A _
S.Map._$₀_ (C.Map.com₁ (C.Map.bwd (G.Mon.t.ƛ mon))) a =
  _ , a
S.Map._$₁_ (C.Map.com₁ (C.Map.bwd (G.Mon.t.ƛ mon))) f =
  _ , f
S.Map.com₁ (C.Map.nat₁ (C.Map.bwd (G.Mon.t.ƛ mon)) {_}{A} g) =
  _ , S.idn A _
S.Map.com₁ (C.Map.com₂ (C.Map.iso-fwd (G.Mon.t.ƛ mon)) {A}) =
  _ , S.idn A _
S.Map.com₁ (C.Map.com₂ (C.Map.iso-bwd (G.Mon.t.ƛ mon)) {A}) =
  S.idn A _

-- ρ
S.Map._$₀_ (C.Map.com₁ (C.Map.fwd (G.Mon.t.ρ mon))) (a , _) =
  a
S.Map._$₁_ (C.Map.com₁ (C.Map.fwd (G.Mon.t.ρ mon))) (f , _) =
  f
S.Map.com₁ (C.Map.nat₁ (C.Map.fwd (G.Mon.t.ρ mon)) {_}{A} _) =
  S.idn A _
S.Map._$₀_ (C.Map.com₁ (C.Map.bwd (G.Mon.t.ρ mon))) a =
  a , _
S.Map._$₁_ (C.Map.com₁ (C.Map.bwd (G.Mon.t.ρ mon))) f =
  f , _
S.Map.com₁ (C.Map.nat₁ (C.Map.bwd (G.Mon.t.ρ mon)) {_}{A} _) =
  S.idn A _ , _
S.Map.com₁ (C.Map.com₂ (C.Map.iso-fwd (G.Mon.t.ρ mon)) {A}) =
  S.idn A _ , _
S.Map.com₁ (C.Map.com₂ (C.Map.iso-bwd (G.Mon.t.ρ mon)) {A}) =
  S.idn A _

-- α
S.Map._$₀_ (C.Map.com₁ (C.Map.fwd (G.Mon.t.α mon))) ((a , b) , c) =
  (a , (b , c))
S.Map._$₁_ (C.Map.com₁ (C.Map.fwd (G.Mon.t.α mon))) ((f , g) , h) =
  (f , (g , h))
S.Map.com₁ (C.Map.nat₁ (C.Map.fwd (G.Mon.t.α mon)) {_}{((A , B) , C)} _) =
  (S.idn A _ , (S.idn B _ , S.idn C _))
S.Map._$₀_ (C.Map.com₁ (C.Map.bwd (G.Mon.t.α mon))) (a , (b , c)) =
  ((a , b) , c)
S.Map._$₁_ (C.Map.com₁ (C.Map.bwd (G.Mon.t.α mon))) (f , (g , h)) =
  ((f , g) , h)
S.Map.com₁ (C.Map.nat₁ (C.Map.bwd (G.Mon.t.α mon)) {_}{((A , B) , C)} _) =
  (S.idn A _ , S.idn B _) , S.idn C _
S.Map.com₁ (C.Map.com₂ (C.Map.iso-fwd (G.Mon.t.α mon)) {((A , B) , C)}) =
  (S.idn A _ , S.idn B _) , S.idn C _
S.Map.com₁ (C.Map.com₂ (C.Map.iso-bwd (G.Mon.t.α mon)) {((A , B) , C)}) =
  S.idn A _ , (S.idn B _ , S.idn C _)

-- triangle law
S.Map.com₁ (G.Mon.t.tri mon {A}{B}) =
  S.idn A _ , S.idn B _

-- pentagon law
S.Map.com₁ (G.Mon.t.pnt mon {A}{B}{C}{D}) =
  S.idn A _ , (S.idn B _ , (S.idn C _ , S.idn D _))
