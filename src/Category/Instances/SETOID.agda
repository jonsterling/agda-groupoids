{-# OPTIONS --without-K #-}

module Category.Instances.SETOID where

open import Agda.Primitive
open import Common
import Category as C
module G where
  open import Groupoid public
  module Mon where
    open import Groupoid.Monoidal public
import Setoid as S
open import Type as T
  using (_,_)

c : ..(ℓᵒ ℓʰ : _) → C.t _ _ _
C.obj (c ℓᵒ ℓʰ) =
  S.t Dir.≈ ℓᵒ ℓʰ
C.homˢ (c _ _) =
  λ {(a , b) → a S.Π.⇒₀ˢ b}
C.idnˢ (c _ _) =
  S.Π.idn₀ˢ
C.cmpˢ (c _ _) =
  S.Π.cmp₀ˢ
S.TF.com₁ (C.idn-lhs (c _ _) {b = B} _) =
  S.idnᵗ B _
S.TF.com₁ (C.idn-rhs (c _ _) {b = B} _) =
  S.idnᵗ B _
S.TF.com₁ (C.cmp-ass (c _ _) {d = D} _ _ _) =
  S.idnᵗ D _
C.invˢ (c _ _) =
  _
C.inv-lhs (c _ _) =
  _
C.inv-rhs (c _ _) =
  _

-- SETOID is a monoidal category
mon
  : ∀ ..{ℓᵒ ℓʰ}
  → G.Mon.t (c ℓᵒ ℓʰ)

-- ⊗
C.Π._$₀_ (G.Mon.t.⊗ mon) (A , B) =
  A S.∐.⊗ B
S.Π._$₀_ (S.Π._$₀_ (C.Π.-$₁ˢ- (G.Mon.t.⊗ mon)) (f₀ , f₁)) (x , y) =
  (f₀ S.Π.$₀ x) , (f₁ S.Π.$₀ y)
S.Π._$₁_ (S.Π._$₀_ (C.Π.-$₁ˢ- (G.Mon.t.⊗ mon)) (f₀ , f₁)) (p , q) =
  (f₀ S.Π.$₁ p) , (f₁ S.Π.$₁ q)
S.TF.com₁ (S.Π._$₁_ (C.Π.-$₁ˢ- (G.Mon.t.⊗ mon)) (p , q))
  = S.TF.com₁ p
  , S.TF.com₁ q
S.TF.com₁ (C.Π.idn (G.Mon.t.⊗ mon) {A , B})
  = S.idnᵗ A _
  , S.idnᵗ B _
S.TF.com₁ (C.Π.cmp (G.Mon.t.⊗ mon) {_}{_}{A , B} _ _)
  = S.idnᵗ A _
  , S.idnᵗ B _

-- 𝟙
G.Mon.t.𝟙 mon =
  S.𝟙.s

-- λ
S.Π._$₀_ (C.TF.com₁ (C.TF.fwd (G.Mon.t.ƛ mon))) (_ , a) =
  a
S.Π._$₁_ (C.TF.com₁ (C.TF.fwd (G.Mon.t.ƛ mon))) (_ , f) =
  f
S.TF.com₁ (C.TF.nat₁ (C.TF.fwd (G.Mon.t.ƛ mon)) {_}{A} _) =
  S.idnᵗ A _
S.Π._$₀_ (C.TF.com₁ (C.TF.bwd (G.Mon.t.ƛ mon))) a =
  _ , a
S.Π._$₁_ (C.TF.com₁ (C.TF.bwd (G.Mon.t.ƛ mon))) f =
  _ , f
S.TF.com₁ (C.TF.nat₁ (C.TF.bwd (G.Mon.t.ƛ mon)) {_}{A} g) =
  _ , S.idnᵗ A _
S.TF.com₁ (C.TF.com₂ (C.TF.iso-fwd (G.Mon.t.ƛ mon)) {A}) =
  _ , S.idnᵗ A _
S.TF.com₁ (C.TF.com₂ (C.TF.iso-bwd (G.Mon.t.ƛ mon)) {A}) =
  S.idnᵗ A _

-- ρ
S.Π._$₀_ (C.TF.com₁ (C.TF.fwd (G.Mon.t.ρ mon))) (a , _) =
  a
S.Π._$₁_ (C.TF.com₁ (C.TF.fwd (G.Mon.t.ρ mon))) (f , _) =
  f
S.TF.com₁ (C.TF.nat₁ (C.TF.fwd (G.Mon.t.ρ mon)) {_}{A} _) =
  S.idnᵗ A _
S.Π._$₀_ (C.TF.com₁ (C.TF.bwd (G.Mon.t.ρ mon))) a =
  a , _
S.Π._$₁_ (C.TF.com₁ (C.TF.bwd (G.Mon.t.ρ mon))) f =
  f , _
S.TF.com₁ (C.TF.nat₁ (C.TF.bwd (G.Mon.t.ρ mon)) {_}{A} _) =
  S.idnᵗ A _ , _
S.TF.com₁ (C.TF.com₂ (C.TF.iso-fwd (G.Mon.t.ρ mon)) {A}) =
  S.idnᵗ A _ , _
S.TF.com₁ (C.TF.com₂ (C.TF.iso-bwd (G.Mon.t.ρ mon)) {A}) =
  S.idnᵗ A _

-- α 
S.Π._$₀_ (C.TF.com₁ (C.TF.fwd (G.Mon.t.α mon))) ((a , b) , c) =
  (a , (b , c))
S.Π._$₁_ (C.TF.com₁ (C.TF.fwd (G.Mon.t.α mon))) ((f , g) , h) =
  (f , (g , h))
S.TF.com₁ (C.TF.nat₁ (C.TF.fwd (G.Mon.t.α mon)) {_}{((A , B) , C)} _) =
  (S.idnᵗ A _ , (S.idnᵗ B _ , S.idnᵗ C _))
S.Π._$₀_ (C.TF.com₁ (C.TF.bwd (G.Mon.t.α mon))) (a , (b , c)) =
  ((a , b) , c)
S.Π._$₁_ (C.TF.com₁ (C.TF.bwd (G.Mon.t.α mon))) (f , (g , h)) =
  ((f , g) , h)
S.TF.com₁ (C.TF.nat₁ (C.TF.bwd (G.Mon.t.α mon)) {_}{((A , B) , C)} _) =
  (S.idnᵗ A _ , S.idnᵗ B _) , S.idnᵗ C _
S.TF.com₁ (C.TF.com₂ (C.TF.iso-fwd (G.Mon.t.α mon)) {((A , B) , C)}) =
  (S.idnᵗ A _ , S.idnᵗ B _) , S.idnᵗ C _
S.TF.com₁ (C.TF.com₂ (C.TF.iso-bwd (G.Mon.t.α mon)) {((A , B) , C)}) =
  S.idnᵗ A _ , (S.idnᵗ B _ , S.idnᵗ C _)

-- triangle law
S.TF.com₁ (G.Mon.t.tri mon {A}{B}) =
  S.idnᵗ A _ , S.idnᵗ B _

-- pentagon law
S.TF.com₁ (G.Mon.t.pnt mon {A}{B}{C}{D}) =
  S.idnᵗ A _ , (S.idnᵗ B _ , (S.idnᵗ C _ , S.idnᵗ D _))
