{-# OPTIONS --without-K #-}

module Category.Instances.SETOID.Closed where

open import Agda.Primitive
open import Common
private
  module C where
    open import Category public
    module I where
      module SETOID where
        open import Category.Instances.SETOID public
private
  module G where
    open import Groupoid public
      hiding (module TF)
    module Clo where
      open import Groupoid.Closed public
        hiding (module G)
    module TF where
      open Groupoid.TF public
      open import Groupoid.Dinatural public
import Setoid as S
open import Type as T
  using (_,_)

-- SETOID is a closed category (incomplete)
clo
  : ∀ ..{ℓ}
  → G.Clo.t (C.I.SETOID.c ℓ ℓ)

-- ⊸
G.Π._$₀_ (G.Clo.t.⊸ clo) (A , B) =
  A S.Π.⇒₀ˢ B
S.Π._$₀_ (S.Π._$₀_ (G.Π.-$₁ˢ- (G.Clo.t.⊸ clo)) (f , g)) h =
  g S.Π.∘₀ h S.Π.∘₀ f
S.TF.com₁ (S.Π._$₁_ (S.Π._$₀_ (G.Π.-$₁ˢ- (G.Clo.t.⊸ clo)) (_ , g)) α) =
  g S.Π.$₁ S.TF.com₁ α
S.TF.com₁ (S.TF.com₁ (S.Π._$₁_ (G.Π.-$₁ˢ- (G.Clo.t.⊸ clo) {_}{_ , D}) {_ , g₀} (α , β)) {h}) =
  S.cmpᵗ D (S.TF.com₁ β , g₀ S.Π.$₁ h S.Π.$₁ S.TF.com₁ α)
S.TF.com₁ (S.TF.com₁ (G.Π.idn (G.Clo.t.⊸ clo) {_ , B})) =
  S.idnᵗ B _
S.TF.com₁ (S.TF.com₁ (G.Π.cmp (G.Clo.t.⊸ clo) {_}{_}{_ , R} _ _)) =
  S.idnᵗ R _

-- 𝟙
G.Clo.t.𝟙 clo =
  S.𝟙.s

-- susp
S.Π._$₀_ (G.TF.com₁ (G.TF.fwd (G.Clo.t.susp clo)) {A}) a =
  S.Π.!ˢ a
S.TF.com₁ (S.Π._$₁_ (G.TF.com₁ (G.TF.fwd (G.Clo.t.susp clo)) {A}) {a}{b} f) =
  f
S.TF.com₁ (S.TF.com₁ (G.TF.nat₁ (G.TF.fwd (G.Clo.t.susp clo)) {_}{B} f)) =
  S.idnᵗ B _
S.Π._$₀_ (G.TF.com₁ (G.TF.bwd (G.Clo.t.susp clo)) {A}) =
  S.Π._$₀ T.𝟙.*
S.Π._$₁_ (G.TF.com₁ (G.TF.bwd (G.Clo.t.susp clo)) {A}) {f₀}{f₁} α =
  S.TF.com₁ α
S.TF.com₁ (G.TF.nat₁ (G.TF.bwd (G.Clo.t.susp clo)) {_}{B} f) =
  S.idnᵗ B _
S.TF.com₁ (G.TF.com₂ (G.TF.iso-fwd (G.Clo.t.susp clo)) {A}) =
  S.idnᵗ A _
S.TF.com₁ (S.TF.com₁ (G.TF.com₂ (G.TF.iso-bwd (G.Clo.t.susp clo)) {A})) =
  S.idnᵗ A _

-- idn
S.Π._$₀_ (G.TF._:⇏₁ᵗ_.com₁ (G.Clo.t.idn clo) {A}) _ =
  S.Π.idn₀ᵗ _
S.TF.com₁ (S.Π._$₁_ (G.TF._:⇏₁ᵗ_.com₁ (G.Clo.t.idn clo) {A}) _) {a} =
  S.idnᵗ A {a} _
S.TF.com₁ (S.TF.com₁ (G.TF._:⇏₁ᵗ_.nat₁ (G.Clo.t.idn clo) {_}{B} f)) =
  S.idnᵗ B _
