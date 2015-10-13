{-# OPTIONS --without-K #-}

module Groupoid.Core.Hom where

open import Agda.Primitive
import Groupoid.Core.Base as G
import Groupoid.Core.Hom.Boot as Π
import Groupoid.Core.Tensor.Boot as ∐
import Groupoid.Core.Homotopy as TF
import Groupoid.Core.Terminal as 𝟙
import Setoid as S
import Setoid.Reasoning
open import Type as T
  using (_,_)

infixr 2 _⇒₀ᵍ_

_⇒₀ᵍ_ : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  → (B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
  → G.t d _ _ _
G.obj (A ⇒₀ᵍ B) =
  A Π.⇒₀ᵗ B
G.homˢ (A ⇒₀ᵍ B) =
  λ {(F , G) → F TF.⇒₁ˢ G}
G.idnˢ (A ⇒₀ᵍ B) =
  λ {F} → TF.idn₁ˢ F
G.cmpˢ (A ⇒₀ᵍ B) =
  TF.cmp₁ˢ
G.invˢ (_⇒₀ᵍ_ {G.Dir.≤} A B) =
  _
G.invˢ (_⇒₀ᵍ_ {G.Dir.≈} A B) =
  TF.inv₁ˢ
TF.com₂ (G.idn-lhs (A ⇒₀ᵍ B) α) =
  G.idn-lhs B (TF.com₁ α)
TF.com₂ (G.idn-rhs (A ⇒₀ᵍ B) α) =
  G.idn-rhs B (TF.com₁ α)
TF.com₂ (G.cmp-ass (A ⇒₀ᵍ B) α β γ) =
  G.cmp-ass B (TF.com₁ α) (TF.com₁ β) (TF.com₁ γ)
G.inv-lhs (_⇒₀ᵍ_ {G.Dir.≤} A B) =
  _
TF.com₂ (G.inv-lhs (_⇒₀ᵍ_ {G.Dir.≈} A B) α) =
  G.inv-lhs B (TF.com₁ α)
G.inv-rhs (_⇒₀ᵍ_ {G.Dir.≤} A B) f =
  _
TF.com₂ (G.inv-rhs (_⇒₀ᵍ_ {G.Dir.≈} A B) α) =
  G.inv-rhs B (TF.com₁ α)

idn₀ᵍ
  : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → {A : G.t d ℓᵒ ℓˢᵒ ℓˢʰ}
  → 𝟙.g Π.⇒₀ᵗ (A ⇒₀ᵍ A)
Π._$₀_ idn₀ᵍ =
  Π.idn₀ᵗ
Π.-$₁ˢ- (idn₀ᵍ {A = A}) =
  G.idnˢ (A ⇒₀ᵍ A)
TF.com₂ (Π.idn (idn₀ᵍ {A = A})) =
  S.idnᵗ (G.homˢ A _) _
TF.com₂ (Π.cmp (idn₀ᵍ {A = A}) g f) =
  S.invᵗ (G.homˢ A _) (G.idn-rhs A (G.idnˢ A S.Π.$₀ _))

cmp₀ᵍ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → ((B ⇒₀ᵍ C) ∐.⊗ (A ⇒₀ᵍ B)) Π.⇒₀ᵗ (A ⇒₀ᵍ C)
Π._$₀_ cmp₀ᵍ =
  Π.cmp₀ᵗ
Π.-$₁ˢ- cmp₀ᵍ =
  TF.cmp₀ˢ-h₀
TF.com₂ (Π.idn (cmp₀ᵍ {B = B}{C}) {g , _}) =
  S.cmpᵗ (G.homˢ C _)
    ( Π.idn g
    , G.idn-rhs C (g Π.$₁ (G.idnˢ B S.Π.$₀ T.𝟙.*)) )
TF.com₂ (Π.cmp (cmp₀ᵍ {C = C}) {c = h₁ , _} (β₁ , _) _) =
  S.cmpᵗ (G.homˢ C _)
    ( S.cmpᵗ (G.homˢ C _)
      ( S.cmpᵗ (G.homˢ C _)
        ( S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _)
        , G.cmpˢ C S.Π.$₁
          ( S.idnᵗ (G.homˢ C _) _
          , S.cmpᵗ (G.homˢ C _)
            ( S.cmpᵗ (G.homˢ C _)
              ( G.cmp-ass C _ _ _
              , G.cmpˢ C S.Π.$₁
                ( S.invᵗ (G.homˢ C _) (TF.nat₁ β₁ _)
                , S.idnᵗ (G.homˢ C _) _ ) )
            , S.invᵗ (G.homˢ C _) (G.cmp-ass C _ _ _) ) ) )
      , G.cmp-ass C _ _ _ )
    , G.cmpˢ C S.Π.$₁ (Π.cmp h₁ _ _ , S.idnᵗ (G.homˢ C _) _) )

!ᵍ
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → G.obj A → (B Π.⇒₀ᵗ A)
Π._$₀_ (!ᵍ a) _ = a
Π.-$₁ˢ- (!ᵍ {A = A} a) = S.Π.!ˢ (G.idnˢ A S.Π.$₀ _)
Π.idn (!ᵍ {A = A} a) = S.idnᵗ (G.homˢ A _) _
Π.cmp (!ᵍ {A = A} a) g f = S.invᵗ (G.homˢ A _) (G.idn-rhs A (G.idnˢ A S.Π.$₀ _))

open import Groupoid.Core.Hom.Boot public
