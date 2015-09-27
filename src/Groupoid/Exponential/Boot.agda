{-# OPTIONS --without-K #-}

module Groupoid.Exponential.Boot where

open import Agda.Primitive
import Groupoid.Base as G
import Setoid as S
open import Type as T
  using (_,_)

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
    -$₁ˢᵐ- : ∀ {a b} → G.homˢ A (a , b) S.Π.⇒₀ᵗ G.homˢ B (_$₀_ a , _$₀_ b)

  _$₁_
    : ∀ {a b}
    → S.obj (G.homˢ A (a , b))
    T.Π.⇒₀ S.obj (G.homˢ B (_$₀_ a , _$₀_ b))
  _$₁_ = λ {_ _} → S.Π._$₀_ -$₁ˢᵐ-

  _$₂_
    : ∀ {a b} {f g : S.obj (G.homˢ A (a , b))}
    → S.homᵗ (G.homˢ A (a , b)) (f , g)
    T.Π.⇒₀ S.homᵗ (G.homˢ B (_$₀_ a , _$₀_ b)) (-$₁ˢᵐ- S.Π.$₀ f , -$₁ˢᵐ- S.Π.$₀ g)
  _$₂_ = λ {_ _ f g} → S.Π._$₁_ -$₁ˢᵐ- {f} {g}

  field
    .idn
      : ∀ {a}
      → S.homᵗ (G.homˢ B (_$₀_ a , _$₀_ a))
          ( -$₁ˢᵐ- S.Π.$₀ (G.idnˢᵐ A {a} S.Π.$₀ T.𝟙.*)
          , G.idnˢᵐ B {_$₀_ a} S.Π.$₀ T.𝟙.*
          )
    .cmp
      : ∀ {a b c}
      → (g : S.obj (G.homˢ A (b , c)))
      → (f : S.obj (G.homˢ A (a , b)))
      → S.homᵗ (G.homˢ B (_$₀_ a , _$₀_ c))
          ( -$₁ˢᵐ- S.Π.$₀ (G.cmpˢᵐ A S.Π.$₀ (g , f))
          , G.cmpˢᵐ B S.Π.$₀ (-$₁ˢᵐ- S.Π.$₀ g , -$₁ˢᵐ- S.Π.$₀ f)
          )
open _⇒₀ᵗ_ public

idnᵗᵐ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → T.𝟙.t⁰ T.Π.⇒₀ (A ⇒₀ᵗ A)
_$₀_ (idnᵗᵐ T.𝟙.*) =
  T.Π.idn
-$₁ˢᵐ- (idnᵗᵐ T.𝟙.*) =
  S.Π.idnᵗᵐ _
idn (idnᵗᵐ {A = A} T.𝟙.*) =
  G.idnˢᵐ A S.Π.$₁ T.𝟙.*
cmp (idnᵗᵐ {A = A} T.𝟙.*) = λ g f →
  G.cmpˢᵐ A S.Π.$₁
    ( S.idnᵗᵐ (G.homˢ A _) T.𝟙.*
    , S.idnᵗᵐ (G.homˢ A _) T.𝟙.*
    )

cmpᵗᵐ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (B ⇒₀ᵗ C) T.∐.⊗ (A ⇒₀ᵗ B) T.Π.⇒₀ (A ⇒₀ᵗ C)
_$₀_ (cmpᵗᵐ (G , F)) =
  T.Π.cmp (G $₀_ , F $₀_)
-$₁ˢᵐ- (cmpᵗᵐ (G , F)) =
  S.Π.cmpᵗᵐ (-$₁ˢᵐ- G , -$₁ˢᵐ- F)
idn (cmpᵗᵐ {C = C} (G , F)) = λ {_} →
  -- FIXME (whiskering)
  S.cmpᵗᵐ (G.homˢ C _)
    ( idn G
    , G $₂ idn F
    )
cmp (cmpᵗᵐ {C = C} (G , F)) = λ {_ _ _} _ _ →
  -- FIXME (whiskering)
  S.cmpᵗᵐ (G.homˢ C _)
    ( cmp G _ _
    , G $₂ (cmp F _ _)
    )

_∘ᵗᵐ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (B ⇒₀ᵗ C) T.Π.⇒₀ (A ⇒₀ᵗ B) T.Π.⇒₀ (A ⇒₀ᵗ C)
_∘ᵗᵐ_ G F = cmpᵗᵐ (G , F)
