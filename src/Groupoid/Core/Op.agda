{-# OPTIONS --without-K #-}

module Groupoid.Core.Op where

open import Agda.Primitive
import Groupoid.Core.Base as G
import Setoid as S
open import Type as T
  using (_,_)

g : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ} → G.t d ℓᵒ ℓˢᵒ ℓˢʰ → G.t d ℓᵒ ℓˢᵒ ℓˢʰ
G.obj (g A) =
  T.Op.t (G.t.obj A)
G.homˢ (g A) =
  G.homˢ A T.Π.∘  T.∐.⟨ T.∐.π₁ , T.∐.π₀ ⟩
G.idnˢ (g A) =
  G.idnˢ A
G.cmpˢ (g A) =
  G.cmpˢ A S.Π.∘₀ S.∐.⟨-,-⟩ S.Π.$₀ (S.∐.π₁ , S.∐.π₀)
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
