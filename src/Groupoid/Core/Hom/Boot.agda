{-# OPTIONS --without-K #-}

module Groupoid.Core.Hom.Boot where

open import Agda.Primitive
import Groupoid.Core.Base as G
import Setoid as S
open import Type as T
  using (_,_)

infixr 1 _⇒₀ᵗ_
infixr 2 _∘₀ᵗ_

record _⇒₀ᵗ_
  {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  (B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ˢᵒ ⊔ ℓ₀ˢʰ) ⊔ (ℓ₁ᵒ ⊔ ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  infixr 4 _$₀_
  infixr 4 _$₁_
  field
    _$₀_ : G.obj A T.Π.⇒₀ G.obj B
    -$₁ˢ- : ∀ {a b} → G.homˢ A (a , b) S.Π.⇒₀ᵗ G.homˢ B (_$₀_ a , _$₀_ b)

  _$₁_
    : ∀ {a b}
    → S.obj (G.homˢ A (a , b))
    T.Π.⇒₀ S.obj (G.homˢ B (_$₀_ a , _$₀_ b))
  _$₁_ = λ {_ _} → S.Π._$₀_ -$₁ˢ-

  ._$₂_
    : ∀ {a b} {f g : S.obj (G.homˢ A (a , b))}
    → S.homᵗ (G.homˢ A (a , b)) (f , g)
    T.Π.⇒₀ S.homᵗ (G.homˢ B (_$₀_ a , _$₀_ b)) (-$₁ˢ- S.Π.$₀ f , -$₁ˢ- S.Π.$₀ g)
  _$₂_ = λ {_ _ f g} → S.Π._$₁_ -$₁ˢ- {f} {g}

  field
    .idn
      : ∀ {a}
      → S.homᵗ (G.homˢ B (_$₀_ a , _$₀_ a))
          ( -$₁ˢ- S.Π.$₀ (G.idnˢ A {a} S.Π.$₀ T.𝟙.*)
          , G.idnˢ B {_$₀_ a} S.Π.$₀ T.𝟙.*
          )
    .cmp
      : ∀ {a b c}
      → (g : S.obj (G.homˢ A (b , c)))
      → (f : S.obj (G.homˢ A (a , b)))
      → S.homᵗ (G.homˢ B (_$₀_ a , _$₀_ c))
          ( -$₁ˢ- S.Π.$₀ (G.cmpˢ A S.Π.$₀ (g , f))
          , G.cmpˢ B S.Π.$₀ (-$₁ˢ- S.Π.$₀ g , -$₁ˢ- S.Π.$₀ f)
          )
open _⇒₀ᵗ_ public

idn₀ᵗ
  : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ}
  → T.𝟙.t⁰ T.Π.⇒₀ (A ⇒₀ᵗ A)
_$₀_ (idn₀ᵗ T.𝟙.*) =
  T.Π.idn
-$₁ˢ- (idn₀ᵗ T.𝟙.*) =
  S.Π.idn₀ᵗ _
idn (idn₀ᵗ {A = A} T.𝟙.*) =
  G.idnˢ A S.Π.$₁ T.𝟙.*
cmp (idn₀ᵗ {A = A} T.𝟙.*) = λ g f →
  G.cmpˢ A S.Π.$₁
    ( S.idnᵗ (G.homˢ A _) T.𝟙.*
    , S.idnᵗ (G.homˢ A _) T.𝟙.*
    )

cmp₀ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (B ⇒₀ᵗ C) T.∐.⊗ (A ⇒₀ᵗ B) T.Π.⇒₀ (A ⇒₀ᵗ C)
_$₀_ (cmp₀ᵗ (G , F)) =
  T.Π.cmp (G $₀_ , F $₀_)
-$₁ˢ- (cmp₀ᵗ (G , F)) =
  S.Π.cmp₀ᵗ (-$₁ˢ- G , -$₁ˢ- F)
idn (cmp₀ᵗ {C = C} (G , F)) = λ {_} →
  -- FIXME (whiskering)
  S.cmpᵗ (G.homˢ C _)
    ( idn G
    , G $₂ idn F
    )
cmp (cmp₀ᵗ {C = C} (G , F)) = λ {_ _ _} _ _ →
  -- FIXME (whiskering)
  S.cmpᵗ (G.homˢ C _)
    ( cmp G _ _
    , G $₂ (cmp F _ _)
    )

_∘₀ᵗ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (B ⇒₀ᵗ C) T.Π.⇒₀ (A ⇒₀ᵗ B) T.Π.⇒₀ (A ⇒₀ᵗ C)
_∘₀ᵗ_ G F = cmp₀ᵗ (G , F)
