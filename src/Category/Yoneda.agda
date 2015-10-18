{-# OPTIONS --without-K #-}

module Category.Yoneda where

open import Agda.Primitive
open import Common
module C where
  module I where
    module SETOID where
      open import Category.Instances.SETOID public
  open import Category public
    hiding (module Map)
  module Map where
    open Category.Map public
    open import Groupoid.Presheaf {Dir.≤} public
import Setoid as S
open import Type as T
  using (_,_)

yo
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → (A : C.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  → A C.Map.⇒₀ᵗ (A C.Map.⇏₀ᵍ C.I.SETOID.c _ _)
C.Map._$₀_ (C.Map._$₀_ (yo A) b) a =
  C.homˢ A (a , b)
S.Map._$₀_ (S.Map._$₀_ (C.Map.-$₁ˢ- (C.Map._$₀_ (yo A) _)) f) g =
  C.cmpˢ A S.Map.$₀ (g , f)
S.Map._$₁_ (S.Map._$₀_ (C.Map.-$₁ˢ- (C.Map._$₀_ (yo A) _)) _) φ =
  C.cmpˢ A S.Map.$₁ (φ , S.idn (C.G.homˢ A _) _)
S.Map.com₁ (S.Map._$₁_ (C.Map.-$₁ˢ- (C.Map._$₀_ (yo A) _)) φ) =
  C.cmpˢ A S.Map.$₁ (S.idn (C.G.homˢ A _) _ , φ)
S.Map.com₁ (C.Map.idn (C.Map._$₀_ (yo A) _)) =
  C.idn-rhs A _
S.Map.com₁ (C.Map.cmp (C.Map._$₀_ (yo A) _) _ _) =
  S.inv (C.G.homˢ A _) (C.cmp-ass A _ _ _)
S.Map._$₀_ (C.Map.com₁ (S.Map._$₀_ (C.Map.-$₁ˢ- (yo A)) _)) _ =
  C.cmpˢ A S.Map.$₀ (_ , _)
S.Map._$₁_ (C.Map.com₁ (S.Map._$₀_ (C.Map.-$₁ˢ- (yo A)) _)) φ =
  C.cmpˢ A S.Map.$₁ (S.idn (C.G.homˢ A _) _ , φ)
S.Map.com₁ (C.Map.nat₁ (S.Map._$₀_ (C.Map.-$₁ˢ- (yo A)) _) _) =
  S.inv (C.G.homˢ A _) (C.cmp-ass A _ _ _)
S.Map.com₁ (C.Map.com₂ (S.Map._$₁_ (C.Map.-$₁ˢ- (yo A)) φ)) =
  C.cmpˢ A S.Map.$₁ (φ , S.idn (C.G.homˢ A _) _)
S.Map.com₁ (C.Map.com₂ (C.Map.idn (yo A))) =
  C.idn-lhs A _
S.Map.com₁ (C.Map.com₂ (C.Map.cmp (yo A) _ _)) =
  C.cmp-ass A _ _ _

oy
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → (A : C.t ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  → A C.Map.⇏₀ᵗ (A C.Map.⇒₀ᵍ C.I.SETOID.c _ _)
C.Map._$₀_ (C.Map._$₀_ (oy A) a) b =
  C.homˢ A (a , b)
S.Map._$₀_ (S.Map._$₀_ (C.Map.-$₁ˢ- (C.Map._$₀_ (oy A) _)) g) f =
  C.cmpˢ A S.Map.$₀ (g , f)
S.Map._$₁_ (S.Map._$₀_ (C.Map.-$₁ˢ- (C.Map._$₀_ (oy A) _)) _) φ =
  C.cmpˢ A S.Map.$₁ (S.idn (C.G.homˢ A _) _ , φ)
S.Map.com₁ (S.Map._$₁_ (C.Map.-$₁ˢ- (C.Map._$₀_ (oy A) _)) φ) =
  C.cmpˢ A S.Map.$₁ (φ , S.idn (C.G.homˢ A _) _)
S.Map.com₁ (C.Map.idn (C.Map._$₀_ (oy A) _)) =
  C.idn-lhs A _
S.Map.com₁ (C.Map.cmp (C.Map._$₀_ (oy A) _) _ _) =
  C.cmp-ass A _ _ _
S.Map._$₀_ (C.Map.com₁ (S.Map._$₀_ (C.Map.-$₁ˢ- (oy A)) _)) _ =
  C.cmpˢ A S.Map.$₀ (_ , _)
S.Map._$₁_ (C.Map.com₁ (S.Map._$₀_ (C.Map.-$₁ˢ- (oy A)) _)) φ =
  C.cmpˢ A S.Map.$₁ (φ , S.idn (C.G.homˢ A _) _)
S.Map.com₁ (C.Map.nat₁ (S.Map._$₀_ (C.Map.-$₁ˢ- (oy A)) _) _) =
  C.cmp-ass A _ _ _
S.Map.com₁ (C.Map.com₂ (S.Map._$₁_ (C.Map.-$₁ˢ- (oy A)) φ)) =
  C.cmpˢ A S.Map.$₁ (S.idn (C.G.homˢ A _) _ , φ)
S.Map.com₁ (C.Map.com₂ (C.Map.idn (oy A))) =
  C.idn-rhs A _
S.Map.com₁ (C.Map.com₂ (C.Map.cmp (oy A) _ _)) =
  S.inv (C.homˢ A _) (C.cmp-ass A _ _ _)
