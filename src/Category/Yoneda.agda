{-# OPTIONS --without-K #-}

module Category.Yoneda where

open import Agda.Primitive
open import Common
module C where
  module I where
    module SETOID where
      open import Category.Instances.SETOID public
  open import Category public
    hiding (module Π)
  module Π where
    open Category.Π public
    open import Groupoid.Presheaf {Dir.≤} public
import Setoid as S
open import Type as T
  using (_,_)

yo
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → (A : C.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  → A C.Π.⇒₀ᵗ (A C.Π.⇏₀ᵍ C.I.SETOID.c _ _)
C.Π._$₀_ (C.Π._$₀_ (yo A) b) a =
  C.homˢ A (a , b)
S.Π._$₀_ (S.Π._$₀_ (C.Π.-$₁ˢ- (C.Π._$₀_ (yo A) _)) f) g =
  C.cmpˢ A S.Π.$₀ (g , f)
S.Π._$₁_ (S.Π._$₀_ (C.Π.-$₁ˢ- (C.Π._$₀_ (yo A) _)) _) φ =
  C.cmpˢ A S.Π.$₁ (φ , S.idnᵗ (C.G.homˢ A _) _)
S.TF.com₁ (S.Π._$₁_ (C.Π.-$₁ˢ- (C.Π._$₀_ (yo A) _)) φ) =
  C.cmpˢ A S.Π.$₁ (S.idnᵗ (C.G.homˢ A _) _ , φ)
S.TF.com₁ (C.Π.idn (C.Π._$₀_ (yo A) _)) =
  C.idn-rhs A _
S.TF.com₁ (C.Π.cmp (C.Π._$₀_ (yo A) _) _ _) =
  S.invᵗ (C.G.homˢ A _) (C.cmp-ass A _ _ _)
S.Π._$₀_ (C.TF.com₁ (S.Π._$₀_ (C.Π.-$₁ˢ- (yo A)) _)) _ =
  C.cmpˢ A S.Π.$₀ (_ , _)
S.Π._$₁_ (C.TF.com₁ (S.Π._$₀_ (C.Π.-$₁ˢ- (yo A)) _)) φ =
  C.cmpˢ A S.Π.$₁ (S.idnᵗ (C.G.homˢ A _) _ , φ)
S.TF.com₁ (C.TF.nat₁ (S.Π._$₀_ (C.Π.-$₁ˢ- (yo A)) _) _) =
  S.invᵗ (C.G.homˢ A _) (C.cmp-ass A _ _ _)
S.TF.com₁ (C.TF.com₂ (S.Π._$₁_ (C.Π.-$₁ˢ- (yo A)) φ)) =
  C.cmpˢ A S.Π.$₁ (φ , S.idnᵗ (C.G.homˢ A _) _)
S.TF.com₁ (C.TF.com₂ (C.Π.idn (yo A))) =
  C.idn-lhs A _
S.TF.com₁ (C.TF.com₂ (C.Π.cmp (yo A) _ _)) =
  C.cmp-ass A _ _ _

oy
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → (A : C.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  → A C.Π.⇏₀ᵗ (A C.Π.⇒₀ᵍ C.I.SETOID.c _ _)
C.Π._$₀_ (C.Π._$₀_ (oy A) a) b =
  C.homˢ A (a , b)
S.Π._$₀_ (S.Π._$₀_ (C.Π.-$₁ˢ- (C.Π._$₀_ (oy A) _)) g) f =
  C.cmpˢ A S.Π.$₀ (g , f)
S.Π._$₁_ (S.Π._$₀_ (C.Π.-$₁ˢ- (C.Π._$₀_ (oy A) _)) _) φ =
  C.cmpˢ A S.Π.$₁ (S.idnᵗ (C.G.homˢ A _) _ , φ)
S.TF.com₁ (S.Π._$₁_ (C.Π.-$₁ˢ- (C.Π._$₀_ (oy A) _)) φ) =
  C.cmpˢ A S.Π.$₁ (φ , S.idnᵗ (C.G.homˢ A _) _)
S.TF.com₁ (C.Π.idn (C.Π._$₀_ (oy A) _)) =
  C.idn-lhs A _
S.TF.com₁ (C.Π.cmp (C.Π._$₀_ (oy A) _) _ _) =
  C.cmp-ass A _ _ _
S.Π._$₀_ (C.TF.com₁ (S.Π._$₀_ (C.Π.-$₁ˢ- (oy A)) _)) _ =
  C.cmpˢ A S.Π.$₀ (_ , _)
S.Π._$₁_ (C.TF.com₁ (S.Π._$₀_ (C.Π.-$₁ˢ- (oy A)) _)) φ =
  C.cmpˢ A S.Π.$₁ (φ , S.idnᵗ (C.G.homˢ A _) _)
S.TF.com₁ (C.TF.nat₁ (S.Π._$₀_ (C.Π.-$₁ˢ- (oy A)) _) _) =
  C.cmp-ass A _ _ _
S.TF.com₁ (C.TF.com₂ (S.Π._$₁_ (C.Π.-$₁ˢ- (oy A)) φ)) =
  C.cmpˢ A S.Π.$₁ (S.idnᵗ (C.G.homˢ A _) _ , φ)
S.TF.com₁ (C.TF.com₂ (C.Π.idn (oy A))) =
  C.idn-rhs A _
S.TF.com₁ (C.TF.com₂ (C.Π.cmp (oy A) _ _)) =
  S.invᵗ (C.homˢ A _) (C.cmp-ass A _ _ _)
