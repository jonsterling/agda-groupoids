{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Op where

open import Agda.Primitive
private
  module G where
    open import Ambient.Groupoid.Base public
    module Map where
      open import Ambient.Groupoid.Map.Boot public
    module Ten where
      open import Ambient.Groupoid.Tensor.Boot public
import Setoid as S
open import Type as T
  using (_,_)

g : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ} → G.t d ℓᵒ ℓˢᵒ ℓˢʰ → G.t d ℓᵒ ℓˢᵒ ℓˢʰ
G.obj (g A) =
  T.Op.t (G.t.obj A)
G.homˢ (g A) =
  G.homˢ A T.Map.∘  T.Ten.⟨ T.Ten.π₁ , T.Ten.π₀ ⟩
G.idnˢ (g A) =
  G.idnˢ A
G.cmpˢ (g A) =
  G.cmpˢ A S.Map.∘₀ (S.Ten.⟨-,-⟩ S.Map.$₀ (S.Ten.π₁ , S.Ten.π₀))
G.invˢ (g A) =
  G.invˢ A
G.idn-lhs (g A) = λ {b a} f →
  G.idn-rhs A f
G.idn-rhs (g A) = λ {b a} f →
  G.idn-lhs A f
G.cmp-ass (g A) = λ {d c b a} h g f →
  S.invᵗ (G.homˢ A (a , d)) (G.cmp-ass A f g h)
G.inv-lhs (g {d = G.Dir.≤} A) = _
G.inv-lhs (g {d = G.Dir.≈} A) = λ {b a} f →
  S.invᵗ (G.homˢ A (b , b)) (G.inv-rhs A f)
G.inv-rhs (g {d = G.Dir.≤} A) = _
G.inv-rhs (g {d = G.Dir.≈} A) = λ {b a} f →
  S.invᵗ (G.homˢ A (a , a)) (G.inv-lhs A f)

⇒
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (F : A G.Map.⇒₀ᵗ B)
  → g A G.Map.⇒₀ᵗ g B
G.Map._$₀_ (⇒ F) =
  F G.Map.$₀_
S.Map._$₀_ (G.Map.-$₁ˢ- (⇒ F)) =
  F G.Map.$₁_
S.Map._$₁_ (G.Map.-$₁ˢ- (⇒ F)) =
  F G.Map.$₂_
G.Map.idn (⇒ F) =
  G.Map.idn F
G.Map.cmp (⇒ {A = A}{B = B} F) {a}{b}{c} g f =
  G.Map.cmp F f g

⊗ : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → A G.Ten.⊗ g B G.Map.⇒₀ᵗ g (g A G.Ten.⊗ B)
G.Map._$₀_ ⊗ =
  T.Map.idn
S.Map._$₀_ (G.Map.-$₁ˢ- ⊗) =
  T.Map.idn
S.Map._$₁_ (G.Map.-$₁ˢ- ⊗) =
  T.Map.idn
G.Map.idn (⊗ {A = A}{B = B}) =
  S.idnᵗ (G.homˢ A _) _ , S.idnᵗ (G.homˢ B _) _
G.Map.cmp (⊗ {A = A}{B = B}) _ _ =
  S.idnᵗ (G.homˢ A _) _ , S.idnᵗ (G.homˢ B _) _
