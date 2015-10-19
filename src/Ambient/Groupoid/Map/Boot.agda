{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Map.Boot where

open import Agda.Primitive
import Ambient.Groupoid.Base as G
import Setoid as S
open import Type as T

infixr 1 _⇒₀ᵗ_
infixr 2 _∘₀ᵗ_

record _⇒₀ᵗ_
  {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  (A : G.𝔊₂,₀ d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  (B : G.𝔊₂,₀ d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ˢᵒ ⊔ ℓ₀ˢʰ) ⊔ (ℓ₁ᵒ ⊔ ℓ₁ˢᵒ ⊔ ℓ₁ˢʰ)) where
  no-eta-equality
  infixr 4 _$₀_
  infixr 4 _$₁_
  field
    _$₀_ : G.obj A ⇒₀,₀ G.obj B
    -$₁ˢ- : ∀ {a b} → G.homˢ A (a , b) S.Map.⇒₀ᵗ G.homˢ B (_$₀_ a , _$₀_ b)

  _$₁_
    : ∀ {a b}
    → S.cell₀ (G.homˢ A (a , b))
    ⇒₀,₀ S.cell₀ (G.homˢ B (_$₀_ a , _$₀_ b))
  _$₁_ = λ {_ _} → S.Map._$₀_ -$₁ˢ-

  ._$₂_
    : ∀ {a b} {f g : S.cell₀ (G.homˢ A (a , b))}
    → S.cell₁ (G.homˢ A (a , b)) (f , g)
    ⇒₀,₀ S.cell₁ (G.homˢ B (_$₀_ a , _$₀_ b)) (-$₁ˢ- S.Map.$₀ f , -$₁ˢ- S.Map.$₀ g)
  _$₂_ = λ {_ _ f g} → S.Map._$₁_ -$₁ˢ- {f} {g}

  field
    .idn
      : ∀ {a}
      → S.cell₁ (G.homˢ B (_$₀_ a , _$₀_ a))
          ( -$₁ˢ- S.Map.$₀ (G.idnˢ A {a} S.Map.$₀ *)
          , G.idnˢ B {_$₀_ a} S.Map.$₀ *
          )
    .cmp
      : ∀ {a b c}
      → (g : S.cell₀ (G.homˢ A (b , c)))
      → (f : S.cell₀ (G.homˢ A (a , b)))
      → S.cell₁ (G.homˢ B (_$₀_ a , _$₀_ c))
          ( -$₁ˢ- S.Map.$₀ (G.cmpˢ A S.Map.$₀ (g , f))
          , G.cmpˢ B S.Map.$₀ (-$₁ˢ- S.Map.$₀ g , -$₁ˢ- S.Map.$₀ f)
          )
open _⇒₀ᵗ_ public

idn₀ᵗ
  : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.𝔊₂,₀ d ℓᵒ ℓˢᵒ ℓˢʰ}
  → 𝟙₀ {lzero} ⇒₀,₀ (A ⇒₀ᵗ A)
_$₀_ (idn₀ᵗ *) =
  ⇒₀.idn₀
-$₁ˢ- (idn₀ᵗ *) =
  S.Map.idn₀ᵗ _
idn (idn₀ᵗ {A = A} *) =
  G.idnˢ A S.Map.$₁ *
cmp (idn₀ᵗ {A = A} *) = λ g f →
  G.cmpˢ A S.Map.$₁
    ( S.idn (G.homˢ A _) *
    , S.idn (G.homˢ A _) *
    )

cmp₀ᵗ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.𝔊₂,₀ d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.𝔊₂,₀ d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.𝔊₂,₀ d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (B ⇒₀ᵗ C) ×₀ (A ⇒₀ᵗ B) ⇒₀,₀ (A ⇒₀ᵗ C)
_$₀_ (cmp₀ᵗ (G , F)) =
  ⇒₀.cmp₀ (G $₀_ , F $₀_)
-$₁ˢ- (cmp₀ᵗ (G , F)) =
  S.Map.cmp₀ᵗ (-$₁ˢ- G , -$₁ˢ- F)
idn (cmp₀ᵗ {C = C} (G , F)) = λ {_} →
  -- FIXME (whiskering)
  S.cmp (G.homˢ C _)
    ( idn G
    , G $₂ idn F
    )
cmp (cmp₀ᵗ {C = C} (G , F)) = λ {_ _ _} _ _ →
  -- FIXME (whiskering)
  S.cmp (G.homˢ C _)
    ( cmp G _ _
    , G $₂ (cmp F _ _)
    )

_∘₀ᵗ_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.𝔊₂,₀ d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.𝔊₂,₀ d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.𝔊₂,₀ d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (B ⇒₀ᵗ C) ⇒₀,₀ (A ⇒₀ᵗ B) ⇒₀,₀ (A ⇒₀ᵗ C)
_∘₀ᵗ_ G F = cmp₀ᵗ (G , F)
