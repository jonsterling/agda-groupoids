{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Op where

open import Agda.Primitive
import Ambient.Groupoid.Base as G
import Setoid as S
open import Type as T

g : ∀ {d} ..{ℓᵒ ℓˢᵒ ℓˢʰ}
  → (A : G.𝔊₂,₀ d ℓᵒ ℓˢᵒ ℓˢʰ)
  → G.𝔊₂,₀ d ℓᵒ ℓˢᵒ ℓˢʰ
G.obj (g A) =
  Op₀ (G.𝔊₂,₀.obj A)
G.homˢ (g A) =
  G.homˢ A ⇒₀.∘₀  ⟨ π¹₀ ,₀ π⁰₀ ⟩
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
  S.inv (G.homˢ A (a , d)) (G.cmp-ass A f g h)
G.inv-lhs (g {d = G.Dir.≤} A) = _
G.inv-lhs (g {d = G.Dir.≈} A) = λ {b a} f →
  S.inv (G.homˢ A (b , b)) (G.inv-rhs A f)
G.inv-rhs (g {d = G.Dir.≤} A) = _
G.inv-rhs (g {d = G.Dir.≈} A) = λ {b a} f →
  S.inv (G.homˢ A (a , a)) (G.inv-lhs A f)
