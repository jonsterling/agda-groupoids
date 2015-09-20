{-# OPTIONS --sized-types --without-K #-}

module Groupoid.Op where

open import Agda.Primitive
import Groupoid.Base as G
import Setoid as S
open import Type as T
  using (_,_)

g : ∀ ..{ℓᵒ ℓˢᵒ ℓˢʰ} → G.t ℓᵒ ℓˢᵒ ℓˢʰ → G.t ℓᵒ ℓˢᵒ ℓˢʰ
G.obj (g A) =
  T.Op.t (G.t.obj A)
G.homˢ (g A) =
  G.homˢ A T.Π.∘  T.∐.⟨ T.∐.π₁ , T.∐.π₀ ⟩
G.idnˢᵐ (g A) =
  G.idnˢᵐ A
G.cmpˢᵐ (g A) =
  G.cmpˢᵐ A S.Π.∘₀ S.∐.⟨-,-⟩ S.Π.$₀ (S.∐.π₁ , S.∐.π₀)
G.invˢᵐ (g A) =
  G.invˢᵐ A
G.idn-lhs (g A) = λ {b a} f →
  S.invᵗᵐ (G.homˢ A (a , b)) (G.idn-rhs A f)
G.idn-rhs (g A) = λ {b a} f →
  S.invᵗᵐ (G.homˢ A (a , b)) (G.idn-lhs A f)
G.cmp-ass (g A) = λ {d c b a} h g f →
  S.invᵗᵐ (G.homˢ A (a , d)) (G.cmp-ass A f g h)
G.inv-lhs (g A) = λ {b a} f →
  S.invᵗᵐ (G.homˢ A (b , b)) (G.inv-rhs A f)
G.inv-rhs (g A) = λ {b a} f →
  S.invᵗᵐ (G.homˢ A (a , a)) (G.inv-lhs A f)
