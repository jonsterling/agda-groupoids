{-# OPTIONS --without-K #-}

open import Common
module Groupoid.Bifunctor {d : Dir.t} where

open import Agda.Primitive
import Groupoid as G
import Setoid as S
open import Type as T
  using (_,_)

module _ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ} where
  infixr 0 :⟨_,_⟩⇒₀ᵗ_
  infixr 2 :⟨_,_⟩⇒₀ᵍ_

  :⟨_,_⟩⇒₀ᵗ_
    : (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → (C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ)
    → Set _
  :⟨ A , B ⟩⇒₀ᵗ C = A G.∐.⊗ B G.Π.⇒₀ᵗ C

  :⟨_,_⟩⇒₀ᵍ_
    : (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
    → (B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    → (C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ)
    → G.t _ _ _ _
  :⟨ A , B ⟩⇒₀ᵍ C = A G.∐.⊗ B G.Π.⇒₀ᵍ C

_:⟨_,-⟩
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (F : :⟨ A , B ⟩⇒₀ᵗ C) (a : G.obj A) → (B G.Π.⇒₀ᵗ C)
G.Π._$₀_ (F :⟨ a ,-⟩) b =
  F G.Π.$₀ (a , b)
S.Π._$₀_ (G.Π.-$₁ˢ- (_:⟨_,-⟩ {A = A} F a)) f =
  F G.Π.$₁ (G.idnˢ A S.Π.$₀ _ , f)
S.Π._$₁_ (G.Π.-$₁ˢ- (_:⟨_,-⟩ {A = A} F a)) p =
  F G.Π.$₂ (S.idnᵗ (G.homˢ A _) _ , p)
G.Π.idn (F :⟨ a ,-⟩) =
  G.Π.idn F
G.Π.cmp (_:⟨_,-⟩ {A = A}{B}{C} F a) {b₀}{b₁}{b₂} g f =
  S.cmpᵗ (G.homˢ C _)
    ( G.Π.cmp F _ _
    , F G.Π.$₂ (G.idn-rhs A _ , S.idnᵗ (G.homˢ B _) _) )

_:⟨-,_⟩
  : ∀ ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (F : :⟨ A , B ⟩⇒₀ᵗ C) (b : G.obj B) → (A G.Π.⇒₀ᵗ C)
G.Π._$₀_ (F :⟨-, b ⟩) a =
  F G.Π.$₀ (a , b)
S.Π._$₀_ (G.Π.-$₁ˢ- (_:⟨-,_⟩ {B = B} F b)) f =
  F G.Π.$₁ (f , G.idnˢ B S.Π.$₀ _)
S.Π._$₁_ (G.Π.-$₁ˢ- (_:⟨-,_⟩ {B = B} F b)) p =
  F G.Π.$₂ (p , S.idnᵗ (G.homˢ B _) _)
G.Π.idn (F :⟨-, b ⟩) =
  G.Π.idn F
G.Π.cmp (_:⟨-,_⟩ {A = A}{B}{C} F b) {a₀}{a₁}{a₂} g f =
  S.cmpᵗ (G.homˢ C _)
    ( G.Π.cmp F _ _
    , F G.Π.$₂ (S.idnᵗ (G.homˢ A _) _ , G.idn-rhs B _) )
