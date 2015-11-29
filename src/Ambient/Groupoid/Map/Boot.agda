{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Map.Boot where

open import Agda.Primitive
import Ambient.Groupoid.Base as G
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
    _$₀_ : G.obj A T.Map.⇒₀ G.obj B
    -$₁ˢ- : ∀ {a b} → G.homˢ A (a , b) S.Map.⇒₀ᵗ G.homˢ B (_$₀_ a , _$₀_ b)

  _$₁_
    : ∀ {a b}
    → S.obj (G.homˢ A (a , b))
    T.Map.⇒₀ S.obj (G.homˢ B (_$₀_ a , _$₀_ b))
  _$₁_ = λ {_ _} → S.Map._$₀_ -$₁ˢ-

  _$₂_
    : ∀ {a b} {f g : S.obj (G.homˢ A (a , b))}
    → S.homᵗ (G.homˢ A (a , b)) (f , g)
    T.Map.⇒₀ S.homᵗ (G.homˢ B (_$₀_ a , _$₀_ b)) (-$₁ˢ- S.Map.$₀ f , -$₁ˢ- S.Map.$₀ g)
  _$₂_ = λ {_ _ f g} → S.Map._$₁_ -$₁ˢ- {f} {g}

  field
    .idn
      : ∀ {a}
      → S.homᵗ (G.homˢ B (_$₀_ a , _$₀_ a))
          ( -$₁ˢ- S.Map.$₀ (G.idnˢ A {a} S.Map.$₀ T.𝟙.*)
          , G.idnˢ B {_$₀_ a} S.Map.$₀ T.𝟙.*
          )
    .cmp
      : ∀ {a b c}
      → (g : S.obj (G.homˢ A (b , c)))
      → (f : S.obj (G.homˢ A (a , b)))
      → S.homᵗ (G.homˢ B (_$₀_ a , _$₀_ c))
          ( -$₁ˢ- S.Map.$₀ (G.cmpˢ A S.Map.$₀ (g , f))
          , G.cmpˢ B S.Map.$₀ (-$₁ˢ- S.Map.$₀ g , -$₁ˢ- S.Map.$₀ f)
          )
open _⇒₀ᵗ_ public

idn₀ᵗ
  : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ}
  → T.𝟙.t⁰ T.Map.⇒₀ (A ⇒₀ᵗ A)
_$₀_ (idn₀ᵗ T.𝟙.*) =
  T.Map.idn
-$₁ˢ- (idn₀ᵗ T.𝟙.*) =
  S.Map.idn₀ᵗ _
idn (idn₀ᵗ {A = A} T.𝟙.*) =
  G.idnˢ A S.Map.$₁ T.𝟙.*
cmp (idn₀ᵗ {A = A} T.𝟙.*) = λ g f →
  G.cmpˢ A S.Map.$₁
    ( S.idnᵗ (G.homˢ A _) T.𝟙.*
    , S.idnᵗ (G.homˢ A _) T.𝟙.*
    )

cmp₀ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (B ⇒₀ᵗ C) T.Ten.⊗ (A ⇒₀ᵗ B) T.Map.⇒₀ (A ⇒₀ᵗ C)
_$₀_ (cmp₀ᵗ (G , F)) =
  T.Map.cmp (G $₀_ , F $₀_)
-$₁ˢ- (cmp₀ᵗ (G , F)) =
  S.Map.cmp₀ᵗ (-$₁ˢ- G , -$₁ˢ- F)
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
  → (B ⇒₀ᵗ C) T.Map.⇒₀ (A ⇒₀ᵗ B) T.Map.⇒₀ (A ⇒₀ᵗ C)
_∘₀ᵗ_ G F = cmp₀ᵗ (G , F)
