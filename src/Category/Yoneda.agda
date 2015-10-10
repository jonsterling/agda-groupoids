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
S.Π._$₀_ (S.Π._$₀_ (C.Π.-$₁ˢᵐ- (C.Π._$₀_ (yo A) _)) f) g =
  C.cmpˢᵐ A S.Π.$₀ (g , f)
S.Π._$₁_ (S.Π._$₀_ (C.Π.-$₁ˢᵐ- (C.Π._$₀_ (yo A) _)) _) φ =
  C.cmpˢᵐ A S.Π.$₁ (φ , S.idnᵗᵐ (C.G.homˢ A _) _)
S.TF.com₁ (S.Π._$₁_ (C.Π.-$₁ˢᵐ- (C.Π._$₀_ (yo A) _)) φ) =
  C.cmpˢᵐ A S.Π.$₁ (S.idnᵗᵐ (C.G.homˢ A _) _ , φ)
S.TF.com₁ (C.Π.idn (C.Π._$₀_ (yo A) _)) =
  S.invᵗᵐ (C.G.homˢ A _) (C.idn-rhs A _)
S.TF.com₁ (C.Π.cmp (C.Π._$₀_ (yo A) _) _ _) =
  S.invᵗᵐ (C.G.homˢ A _) (C.cmp-ass A _ _ _)
S.Π._$₀_ (C.TF.com₁ (S.Π._$₀_ (C.Π.-$₁ˢᵐ- (yo A)) _)) _ =
  C.cmpˢᵐ A S.Π.$₀ (_ , _)
S.Π._$₁_ (C.TF.com₁ (S.Π._$₀_ (C.Π.-$₁ˢᵐ- (yo A)) _)) φ =
  C.cmpˢᵐ A S.Π.$₁ (S.idnᵗᵐ (C.G.homˢ A _) _ , φ)
S.TF.com₁ (C.TF.nat₁ (S.Π._$₀_ (C.Π.-$₁ˢᵐ- (yo A)) _) _) =
  S.invᵗᵐ (C.G.homˢ A _) (C.cmp-ass A _ _ _)
S.TF.com₁ (C.TF.com₂ (S.Π._$₁_ (C.Π.-$₁ˢᵐ- (yo A)) φ)) =
  C.cmpˢᵐ A S.Π.$₁ (φ , S.idnᵗᵐ (C.G.homˢ A _) _)
S.TF.com₁ (C.TF.com₂ (C.Π.idn (yo A))) =
  C.idn-lhs A _
S.TF.com₁ (C.TF.com₂ (C.Π.cmp (yo A) _ _)) =
  C.cmp-ass A _ _ _
